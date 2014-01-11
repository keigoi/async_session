(* compile with OCaml 3.10.0+varunion *)

module type SESSION = sig
  (* slots *)                     
  type (+'hd, +'tl) cons

  (* empty slot(s) *)
  type empty
  type all_empty = (empty, 'a) cons as 'a

  
  (*
   * index to specify usage-tracked `slots'.
   * the type is to read
   *   "in the slot a, replace the n-th content of type an with that of type bn.
   *    the resulting slot is b."
   *)
  type ('an,'bn,'a,'b) idx
  
                       
  val _0 : ('a0, 'b0, ('a0,'a) cons, ('b0,'a) cons) idx
  val _1 : ('a1, 'b1, ('a0,('a1,'a) cons) cons, ('a0,('b1,'a) cons) cons) idx
  val _2 : ('a2, 'b2, ('a0,('a1,('a2,'a) cons) cons) cons, ('a0,('a1,('b2,'a) cons) cons) cons) idx
  val _3 : ('a3, 'b3, ('a0,('a1,('a2,('a3,'a) cons) cons) cons) cons, ('a0,('a1,('a2,('b3,'a) cons) cons) cons) cons) idx
  val succ : ('an, 'bn, 'a, 'b) idx -> ('an, 'bn, ('a0,'a) cons, ('a0,'b) cons) idx
  
  (* variable-type-state monad *)
  type ('p,'q,'a) monad
  val ret : 'a -> ('p, 'p, 'a) monad
  val (>>=) : ('p,'q,'a) monad -> ('a -> ('q,'r,'b) monad) -> ('p,'r,'b) monad
  val (>>) : ('p,'q,'a) monad -> ('q,'r,'b) monad -> ('p,'r,'b) monad

  (* these tags are used to express 'polarity' (indicating an endpoint of a channel) *)
  type pos and neg

  (*
   * the type of channels, which are embedded in slots and not escaped outside the monad.
   * pair of 's and 't shows polarity ('s != 't).
   * every channels have type of either:
   *     (pos, neg, 'k) channel (i.e. 'positive'-side)
   *  or
   *     (neg, pos, 'k) channel (i.e. 'negative'-side)
   *)
  type ('s, 't, 'k) channel
  type 'k cont
          
  (*
   * a session type associated to a channel is represented in a symmetric manner.
   * the type of sending an integer twice has either:
   * <for positive side>
   *   (pos, neg, [`Shot of pos * int * 'k cont]) channel
   * or
   * <for negative side>
   *   (neg, pos, [`Shot of neg * int * 'k cont]) channel
   *
   * symmetrically, channel receiving of an int has the type of either
   *   (pos, neg, [`Shot of neg * int * 'k cont]) channel
   * or
   *   (neg, pos, [`Shot of pos * int * 'k cont]) channel
   *)
                    
  val send : (('s,'t,[>`Shot of 's * 'a * 'k cont])channel , ('s,'t,'k) channel, 'p, 'q) idx -> 'a -> ('p,'q,unit) monad
  val recv : (('s,'t,[`Shot of 't * 'a * 'k cont])channel, ('s,'t,'k) channel, 'p, 'q) idx -> ('p,'q,'a) monad
  val close : (('s,'t,[>`Finish])channel, empty, 'p, 'q) idx -> ('p, 'q, unit) monad
  
  val send_slot : 
    (('s,'t,[>`Pass of 's * 'c * 'k cont]) channel, ('s,'t,'k) channel, 'q, 'r) idx -> 
    ('c, empty, 'p, 'q) idx ->
    ('p,'r,unit) monad
  
  val recv_slot :
    (('s,'t,[`Pass of 't * 'c * 'k cont]) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
    (empty, 'c, 'q, 'r) idx ->
    ('p,'r,unit) monad
  
  val send_chan : 
    (('s,'t,[>`Pass of 's * ('ss,'tt,'kk)channel * 'k cont]) channel, ('s,'t,'k) channel, 'q, 'r) idx -> 
    (('ss,'tt,'kk)channel, empty, 'p, 'q) idx ->
    ('p,'r,unit) monad
  
  val recv_chan :
    (('s,'t,[`Pass of 't * ('ss,'tt,'kk)channel * 'k cont]) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
    (empty, ('ss,'tt,'kk)channel, 'q, 'r) idx ->
    ('p,'r,unit) monad
  
  val send_new_chan : 
    (('s,'t,[>`Pass of 's * ('t,'s,'kk)channel * 'k cont]) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
    (empty,('s,'t,'kk)channel, 'q, 'r) idx ->
    ('p,'r,unit) monad
  
  val fork : 
    (empty, (pos,neg,'k)channel, 'p, 'q) idx -> 
    (((neg,pos,'k)channel, all_empty) cons, all_empty, unit) monad -> 
    ('p,'q,unit) monad

  (*
   * synthesize branching on arbitrary-many `tags
   * here after we need union of abstract poly-variants
   *)

  (*
   * Basic signature of the synthesis
   *)
  module type BRANCH = sig
    (* session  *)
    type 't from = private [> ]
    (* type of the branch *)
    type ('s,'t,'q,'r,'a) branch

    (* used internally *)
    val cont_ : 's -> 'q -> ('r * 'a) cont -> ('s,'t,'q,'r,'a) branch -> 't from -> unit

    (* synthesized branch *)
    val branch : (('s,'t,'t from)channel,empty,'p,'q) idx ->
                  ('s,'t,'q,'r,'a) branch ->
                  ('p,'r,'a) monad
  end

  (* branch `Finish *)
  module BranchFinish :
      BRANCH with
           type 't from = [`Finish] and
           type ('s,'t,'q,'r,'a) branch = unit -> ('q,'r,'a) monad

  type ('s,'t,'v,'k,'q,'r,'a) on_receive =
      {on_receive:'q1. (empty,('s,'t,'k)channel, 'q,'q1) idx * ('v -> ('q1,'r,'a) monad)}
  (* FAIL: we need 'q1 to be existential, not universal. *)

  module type SHOT = sig
      type 'a polyvar = private [> ]
      type v
      type k
      val ext : 'a polyvar -> 'a
    end

  (* Receiving (`SomeTag of 't * 'v * 'k) *)
  module BranchRecv :
    functor (X:SHOT) ->
      BRANCH with
           type 't from = [< ('t * X.v * X.k cont) X.polyvar] and (* '<' is strange but compiles for now *)
           type ('s,'t,'q,'r,'a) branch = ('s, 't,X.v,X.k,'q,'r,'a) on_receive

  (* adding another tag. HERE WE USE UNION OF ABSTRACT VARIANTS *)
  module BranchAddRecv :
    functor (M:BRANCH) -> functor (X:SHOT with type 'a polyvar = private [> ]~[M.from]) ->
      BRANCH with
           type 't from = ['t M.from | ('t * X.v * X.k cont) X.polyvar] and (* HERE *)
           type ('s,'t,'q,'r,'a) branch = ('s,'t,'q,'r,'a) M.branch * ('s,'t,X.v,X.k,'q,'r,'a) on_receive
end

(* signature of Ivar in Janestreet Async *)
module type IVAR = sig
    type 'a t

    val create : unit -> _ t
    val create_full : 'a -> 'a t

    val peek     : 'a t -> 'a option
    val is_empty : _ t -> bool
    val is_full  : _ t -> bool

    val equal : 'a t -> 'a t -> bool

    val connect : bind_result:'a t -> bind_rhs:'a t -> unit
    val fill : 'a t -> 'a  -> unit


    val upon  : 'a t -> ('a -> unit) -> unit

  end
                     
module Session(Ivar:IVAR) : SESSION = struct
    
  type ('a,'b,'p,'q) idx = ('p -> 'a) * ('p -> 'b -> 'q)
  type ('hd, 'tl) cons = 'hd * 'tl
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
  
  
  let rec all_empty = Empty, all_empty
  
  type pos = Pos and neg = Neg
  
  type ('s,'v,'k) shot = Shot of 's * 'v * 'k Ivar.t
  type ('s,'c,'k) pass = Pass of 's * 'c * 'k Ivar.t
  type ('s,'k1,'k2) branch = BranchLeft of 's * 'k1 Ivar.t | BranchRight of 's * 'k2 Ivar.t
  type finish = unit
  type ('s,'t,'v,'w,'k) yield = ('s,'v,('t,'w,'k)shot)shot
  
  type ('s,'t,'k) channel = Chan of 's * 't * 'k Ivar.t
  type 'k cont = 'k Ivar.t
  
  let send (get,set) v p =
    let Chan(s,t,c) = get p in
    let c' = Ivar.create () in
    Ivar.fill c (`Shot(s,v,c'));
    Ivar.create_full (set p (Chan(s,t,c')), ())
                                     
  let recv (get,set) p =
    let Chan(s,t,c) = get p in
    let ret = Ivar.create () in
    Ivar.upon c (fun (`Shot(_, v, c')) -> Ivar.fill ret (set p (Chan(s,t,c')), v));
    ret
  
  let close (get,set) p =
    Ivar.create_full (set p Empty, ())
  
  let send_slot (get0,set0) (get1,set1) p =
    let e, q = get1 p, set1 p Empty in
    let Chan(s,t,c) = get0 q in
    let c' = Ivar.create () in
    Ivar.fill c (`Pass(s,e,c'));
    Ivar.create_full (set0 q (Chan(s,t,c')), ())
  
  let send_chan = send_slot
                   
  let recv_slot (get0,set0) (get1,set1) p =
    let Chan(s,t,c) = get0 p in
    let ret = Ivar.create () in
    Ivar.upon c (fun (`Pass(_,e,c')) -> Ivar.fill ret (set1 (set0 p (Chan(s,t,c'))) e, ()));
    ret
  
  let recv_chan = recv_slot
  
  let send_new_chan (get0,set0) (get1,set1) p =
    let Chan(s,t,c) = get0 p in
    let c' = Ivar.create () in
    let cc = Ivar.create () in
    let e = `Pass(s,Chan(t,s,cc),c') in
    Ivar.fill c e;
    Ivar.create_full (set1 (set0 p (Chan(s,t,c'))) (Chan(s,t,cc)), ())
  
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
  
  
  let fork (get,set) m p =
    let ivar = Ivar.create () in
    ignore (m (Chan(Neg,Pos,ivar),all_empty));
    Ivar.create_full (set p (Chan(Pos,Neg,ivar)), ())

  module type BRANCH = sig
    type 't from = private [> ]
    type ('s,'t,'q,'r,'a) branch
    val cont_ : 's -> 'q -> ('r * 'a) cont -> ('s,'t,'q,'r,'a) branch -> 't from -> unit
    val branch : (('s,'t,'t from)channel,empty,'p,'q) idx ->
                  ('s,'t,'q,'r,'a) branch ->
                  ('p,'r,'a) monad
  end

  module BranchFinish = struct
    type 't from = [`Finish]
    type ('s,'t,'q,'r,'a) branch = unit -> ('q,'r,'a) monad
    let cont_ s q ret on_close `Finish =
      Ivar.connect ~bind_rhs:(on_close () q) ~bind_result:ret
    let branch (get0,set0) go p =
      let Chan(s,t,c), q = get0 p, set0 p Empty
      and ret = Ivar.create ()
      in
      Ivar.upon c (cont_ s q ret go);
      ret
  end

  module type SHOT = sig
      type 'a polyvar = private [> ]
      type v
      type k
      val ext : 'a polyvar -> 'a
    end
                     
  type ('s,'t,'v,'k,'q,'r,'a) on_receive =
      {on_receive:'q1. (empty,('s,'t,'k)channel, 'q,'q1) idx * ('v -> ('q1,'r,'a) monad)}
      
  module BranchRecv = functor (X:SHOT) -> struct
    type 't from = [< ('t * X.v * X.k cont) X.polyvar]
    type ('s,'t,'q,'r,'a) branch = ('s, 't, X.v, X.k, 'q, 'r, 'a) on_receive

    let cont_ s q ret go (#X.polyvar as x) =
      let (t,v,c') = X.ext x
      and (get1,set1), go = go.on_receive
      in
      Ivar.connect ~bind_rhs:(go v (set1 q (Chan(s,t,c')))) ~bind_result:ret

    let branch (get0,set0) go p =
      let Chan(s,t,c), q = get0 p, set0 p Empty
      and ret = Ivar.create ()
      in
      Ivar.upon c (cont_ s q ret go);
      ret
  end

  module BranchAddRecv(M:BRANCH)(X:SHOT with type 'a polyvar = private [> ]~[M.from]) = struct
    type 't from = ['t M.from | ('t * X.v * X.k cont) X.polyvar]
    type ('s,'t,'q,'r,'a) branch = ('s,'t,'q,'r,'a) M.branch * ('s,'t,X.v,X.k,'q,'r,'a) on_receive

    let cont_ s q ret (go1,go2) = function
      | #M.from as x ->
        M.cont_ s q ret go1 x
      | #X.polyvar as x ->
        let (t,v,c') = X.ext x
        and (get1,set1), go2 = go2.on_receive
        in
        Ivar.connect ~bind_rhs:(go2 v (set1 q (Chan(s,t,c')))) ~bind_result:ret
    let branch (get0,set0) go p =
      let Chan(s,t,c), q = get0 p, set0 p Empty
      and ret = Ivar.create ()
      in
      Ivar.upon c (cont_ s q ret go);
      ret
  end
end

module BranchSynthesisExample(Ivar:IVAR) = struct
  module S = Session(Ivar)
  open S
         
  let branch_close_or_shot1 () =
    let module Shot1 = struct
      type 'a polyvar = [`Shot1 of 'a]
      type v = int
      type k = [`Finish]
      let ext (`Shot1(x)) = x
    end in
    let module M =
      BranchAddRecv(BranchFinish)(Shot1)
    in M.branch
         
  let branch_shot1_or_shot2 () =
    let module Shot1 = struct
      type 'a polyvar = [`Shot1 of 'a]
      type v = int
      type k = [`Finish]
      let ext (`Shot1(x)) = x
    end in
    let module Shot2 = struct
      type 'a polyvar = [`Shot2 of 'a]
      type v = string
      type k = [`Finish]
      let ext (`Shot2(x)) = x
    end in
    let module M = BranchAddRecv(BranchRecv(Shot1))(Shot2)
    in M.branch
end


