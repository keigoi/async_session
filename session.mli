type ('an,'bn,'a,'b) idx
type (+'hd, +'tl) slot

type empty
type all_empty = (empty, 'a) slot as 'a

val _0 : ('a0, 'b0, ('a0,'a) slot, ('b0,'a) slot) idx
val _1 : ('a1, 'b1, ('a0,('a1,'a) slot) slot, ('a0,('b1,'a) slot) slot) idx
val _2 : ('a2, 'b2, ('a0,('a1,('a2,'a) slot) slot) slot, ('a0,('a1,('b2,'a) slot) slot) slot) idx
val _3 : ('a3, 'b3, ('a0,('a1,('a2,('a3,'a) slot) slot) slot) slot, ('a0,('a1,('a2,('b3,'a) slot) slot) slot) slot) idx
val succ : ('an, 'bn, 'a, 'b) idx -> ('an, 'bn, ('a0,'a) slot, ('a0,'b) slot) idx

type ('p,'q,'a) monad
val ret : 'a -> ('p, 'p, 'a) monad
val (>>=) : ('p,'q,'a) monad -> ('a -> ('q,'r,'b) monad) -> ('p,'r,'b) monad
val (>>) : ('p,'q,'a) monad -> ('q,'r,'b) monad -> ('p,'r,'b) monad
val slide : ('p,'q,'a) monad -> (('p0,'p)slot,('p0,'q)slot,'a) monad

val run : (all_empty,all_empty,'a) monad -> 'a Async.Std.Deferred.t

type ('s, 'v, 'k) shot
type ('s, 'c, 'k) pass
type ('s, 'k1, 'k2) branch
type fini
type ('s,'t,'v,'w,'k) yield = ('s,'v,('t,'w,'k)shot)shot
       
type pos and neg

type ('s, 't, 'k) sess
                  
val send : (('s,'t,('t,'a,'k)shot)sess , ('s,'t,'k) sess, 'p, 'q) idx -> 'a -> ('p,'q,unit) monad
val recv : (('s,'t,('s,'a,'k)shot)sess, ('s,'t,'k) sess, 'p, 'q) idx -> ('p,'q,'a) monad
val close : (('s,'t,fini)sess, empty, 'p, 'q) idx -> ('p, 'q, unit) monad

val send_slot : 
  (('s,'t,('t,'c,'k) pass) sess, ('s,'t,'k) sess, 'q, 'r) idx -> 
  ('c, empty, 'p, 'q) idx ->
  ('p,'r,unit) monad

val recv_slot :
  (('s,'t,('s,'c,'k) pass) sess, ('s,'t,'k) sess, 'p, 'q) idx -> 
  (empty, 'c, 'q, 'r) idx ->
  ('p,'r,unit) monad

val send_chan : 
  (('s,'t,('t,('ss,'tt,'kk)sess,'k) pass) sess, ('s,'t,'k) sess, 'q, 'r) idx -> 
  (('ss,'tt,'kk)sess, empty, 'p, 'q) idx ->
  ('p,'r,unit) monad

val recv_chan :
  (('s,'t,('s,('ss,'tt,'kk)sess,'k) pass) sess, ('s,'t,'k) sess, 'p, 'q) idx -> 
  (empty, ('ss,'tt,'kk)sess, 'q, 'r) idx ->
  ('p,'r,unit) monad

val send_new_chan : 
  (('s,'t,('t,('t,'s,'kk)sess,'k) pass) sess, ('s,'t,'k) sess, 'p, 'q) idx -> 
  (empty,('s,'t,'kk)sess, 'q, 'r) idx ->
  ('p,'r,unit) monad
               
val select_left :
  (('s,'t,('t,'k1,'k2)branch)sess, ('s,'t,'k1)sess, 'p, 'q) idx ->
  ('p,'q,unit) monad
val select_right :
  (('s,'t,('t,'k1,'k2)branch)sess, ('s,'t,'k2)sess, 'p, 'q) idx ->
  ('p,'q,unit) monad
val branch : 
  (('s,'t,('s,'k1,'k2)branch)sess, empty, 'p, 'q) idx ->
  (empty,('s,'t,'k1)sess, 'q,'q1) idx * (unit -> ('q1,'r,'a) monad) ->
  (empty,('s,'t,'k2)sess, 'q,'q2) idx * (unit -> ('q2,'r,'a) monad) ->
  ('p,'r,'a) monad

val fork : 
  new_chan:(empty, (pos,neg,'k)sess, 'p, 'q) idx -> 
  (((neg,pos,'k)sess, all_empty) slot, all_empty, unit) monad -> 
  ('p,'q,unit) monad

module LinList : sig
  val nil : (empty,'a list,'p,'q) idx -> ('p,'q,unit) monad
  val put : ('a list,'a list,'q,'r) idx -> ('a,empty,'p,'q) idx -> ('p,'r,unit)monad
  val take : ('a list,'a list,'p,'p) idx * (empty,'a,'p,'q1) idx * (unit -> ('q1,'r,'b) monad) ->
             ('a list,empty,'p,'q2) idx * (unit -> ('q2,'r,'b) monad) ->
             ('p,'r,'b) monad
  (*val map : ('a list,'b list,'p,'q) idx -> ('c -> (('a,all_empty)slot,('b,all_empty)slot,'c)monad) -> 'c -> ('p,'q,'c) monad*)
end
               
module Routine : sig
  val send : 'v -> (('s,'t,('t,'v,'k)shot)sess, ('s,'t,'k) sess, unit) monad
  val recv : (('s,'t,('s,'v,'k)shot)sess, ('s,'t,'k) sess, 'v) monad
  val close : (('s,'t,fini)sess, empty, unit) monad
  val yield : 'v -> (('s,'t,('t,'t,'v,'w,'k)yield)sess, ('s,'t,'k)sess, 'w) monad
end

val run_routine :
  (empty, (pos,neg,'k)sess, 'p, 'q) idx ->
  ((neg,pos,'k)sess, empty, unit) monad ->
  ('p,'q,unit) monad
