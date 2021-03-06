module Ivar = Async_core.Raw_ivar
module Scheduler = Async.Std.Scheduler                

type ('a,'b,'p,'q) idx = ('p -> 'a) * ('p -> 'b -> 'q)
type ('hd, 'tl) slot = 'hd * 'tl
type empty = Empty
type all_empty = empty * all_empty

let _0 = (fun (a0,_) -> a0), (fun (_,a) b0 -> (b0,a))
let _1 = (fun (_,(a1,_)) -> a1), (fun (a0,(_,a)) b1 -> (a0,(b1,a)))
let _2 = (fun (_,(_,(a2,_))) -> a2), (fun (a0,(a1,(_,a))) b2 -> (a0,(a1,(b2,a))))
let _3 = (fun (_,(_,(_,(a3,_)))) -> a3), (fun (a0,(a1,(a2,(_,a)))) b3 -> (a0,(a1,(a2,(b3,a)))))
let succ (get,set) = (fun (_,a) -> get a), (fun (a0,a) bn -> (a0,set a bn))

type ('p,'q,'a) monad = 'p -> ('q * 'a) Ivar.t
let ret a p = Ivar.create_full (p, a)
let (>>=) m f p =
  let ret = Ivar.create () in
  Ivar.upon (m p) (fun (q, x) -> Ivar.connect ~bind_rhs:(f x q) ~bind_result:ret);
  ret
let (>>) m n = m >>= (fun _ -> n)
let slide m (p0,p) =
  let ret = Ivar.create () in
  Ivar.upon (m p) (fun (q, x) -> Ivar.fill ret ((p0,q),x));
  ret


let rec all_empty = Empty, all_empty
let run m =
  Async.Std.Deferred.create
    (fun iv -> Ivar.upon (m all_empty) (fun (_, x) -> Async.Std.Ivar.fill iv x))

type pos = Pos and neg = Neg

type ('s,'v,'k) shot = Shot of 's * 'v * 'k Ivar.t
type ('s,'c,'k) pass = Pass of 's * 'c * 'k Ivar.t
type ('s,'k1,'k2) branch = BranchLeft of 's * 'k1 Ivar.t | BranchRight of 's * 'k2 Ivar.t
type fini = unit
type ('s,'t,'v,'w,'k) yield = ('s,'v,('t,'w,'k)shot)shot

type ('s,'t,'k) sess = Chan of 's * 't * 'k Ivar.t

let send (get,set) v p =
  let Chan(s,t,c) = get p in
  let c' = Ivar.create () in
  Ivar.fill c (Shot(t,v,c'));
  Ivar.create_full (set p (Chan(s,t,c')), ())
                                   
let recv (get,set) p =
  let Chan(s,t,c) = get p in
  let ret = Ivar.create () in
  Ivar.upon c (fun (Shot(_, v, c')) -> Ivar.fill ret (set p (Chan(s,t,c')), v));
  ret

let close (get,set) p =
  Ivar.create_full (set p Empty, ())

let send_slot (get0,set0) (get1,set1) p =
  let e, q = get1 p, set1 p Empty in
  let Chan(s,t,c) = get0 q in
  let c' = Ivar.create () in
  Ivar.fill c (Pass(t,e,c'));
  Ivar.create_full (set0 q (Chan(s,t,c')), ())

let send_chan = send_slot
                 
let recv_slot (get0,set0) (get1,set1) p =
  let Chan(s,t,c) = get0 p in
  let ret = Ivar.create () in
  Ivar.upon c (fun (Pass(_,e,c')) -> Ivar.fill ret (set1 (set0 p (Chan(s,t,c'))) e, ()));
  ret

let recv_chan = recv_slot

let send_new_chan (get0,set0) (get1,set1) p =
  let Chan(s,t,c) = get0 p in
  let c' = Ivar.create () in
  let cc = Ivar.create () in
  let e = Pass(t,Chan(t,s,cc),c') in
  Ivar.fill c e;
  Ivar.create_full (set1 (set0 p (Chan(s,t,c'))) (Chan(s,t,cc)), ())

let select_left (get,set) p =
  let Chan(s,t,c) = get p in
  let c' = Ivar.create () in
  Ivar.fill c (BranchLeft(t,c'));
  Ivar.create_full (set p (Chan(s,t,c')), ())
                       
let select_right (get,set) p =
  let Chan(s,t,c) = get p in
  let c' = Ivar.create () in
  Ivar.fill c (BranchRight(t,c'));
  Ivar.create_full (set p (Chan(s,t,c')), ())

let branch (get0,set0) ((get1,set1),f1) ((get2,set2),f2) p =
  let Chan(s,t,c), q = get0 p, set0 p Empty in
  let ret = Ivar.create () in
  Ivar.upon c
            (function
              | BranchLeft(_,c') ->
                 Ivar.connect ~bind_rhs:(f1 () (set1 q (Chan(s,t,c')))) ~bind_result:ret
              | BranchRight(_,c') ->
                 Ivar.connect ~bind_rhs:(f2 () (set2 q (Chan(s,t,c')))) ~bind_result:ret
            );
  ret


let fork ~new_chan:(get,set) m p =
  let ivar = Ivar.create () in
  Scheduler.within (fun _ -> ignore (m (Chan(Neg,Pos,ivar),all_empty)));
  Ivar.create_full (set p (Chan(Pos,Neg,ivar)), ())

module LinList = struct                   
  let nil (_,set) p = Ivar.create_full (set p [], ())
  let put (get0,set0) (get1,set1) p =
    let q = set1 p Empty in
    Ivar.create_full (set0 q (get1 p::get0 q), ())
  let take ((get0,set0),(get1,set1),f0) ((_,set2),f2) p =
    match get0 p with
    | x::xs ->
       let ret = Ivar.create () in
       Ivar.upon (f0 () (set1 (set0 p xs) x)) (Ivar.fill ret);
       ret
    | [] -> f2 () (set2 p Empty)
end

module Routine = struct
  let send v (Chan(s,t,c)) =
    let c' = Ivar.create () in
    Ivar.fill c (Shot(t,v,c'));
    Ivar.create_full (Chan(s,t,c'),())
  
  let recv (Chan(s,t,c)) =
    let ret = Ivar.create () in
    Ivar.upon c (fun (Shot(_,v,c')) -> Ivar.fill ret (Chan(s,t,c'),v));
    ret
  
  let close (Chan(_,_,_)) =
    Ivar.create_full (Empty, ())

  let yield v = send v >> recv
end

let run_routine (get,set) m p =
  let c = Ivar.create () in
  m (Chan(Neg,Pos,c));
  Ivar.create_full (set p (Chan(Pos,Neg,c)), ())
                 
