type ('an,'bn,'a,'b) idx
type (+'hd, +'tl) cons

type empty
type all_empty = (empty, 'a) cons as 'a

val _0 : ('a0, 'b0, ('a0,'a) cons, ('b0,'a) cons) idx
val _1 : ('a1, 'b1, ('a0,('a1,'a) cons) cons, ('a0,('b1,'a) cons) cons) idx
val _2 : ('a2, 'b2, ('a0,('a1,('a2,'a) cons) cons) cons, ('a0,('a1,('b2,'a) cons) cons) cons) idx
val _3 : ('a3, 'b3, ('a0,('a1,('a2,('a3,'a) cons) cons) cons) cons, ('a0,('a1,('a2,('b3,'a) cons) cons) cons) cons) idx
val succ : ('an, 'bn, 'a, 'b) idx -> ('an, 'bn, ('a0,'a) cons, ('a0,'b) cons) idx

type ('p,'q,'a) monad
val ret : 'a -> ('p, 'p, 'a) monad
val (>>=) : ('p,'q,'a) monad -> ('a -> ('q,'r,'b) monad) -> ('p,'r,'b) monad
val (>>) : ('p,'q,'a) monad -> ('q,'r,'b) monad -> ('p,'r,'b) monad
val slide : ('p,'q,'a) monad -> (('p0,'p)cons,('p0,'q)cons,'a) monad

val run : (all_empty,all_empty,'a) monad -> 'a Async.Std.Deferred.t

type ('s, 'v, 'k) shot
type ('s, 'c, 'k) pass
type ('s, 'k1, 'k2) branch
type finish
type ('s,'t,'v,'w,'k) yield = ('s,'v,('t,'w,'k)shot)shot
       
type pos and neg

type ('s, 't, 'k) channel
                  
val send : (('s,'t,('s,'a,'k)shot)channel , ('s,'t,'k) channel, 'p, 'q) idx -> 'a -> ('p,'q,unit) monad
val recv : (('s,'t,('t,'a,'k)shot)channel, ('s,'t,'k) channel, 'p, 'q) idx -> ('p,'q,'a) monad
val close : (('s,'t,finish)channel, empty, 'p, 'q) idx -> ('p, 'q, unit) monad

val send_slot : 
  (('s,'t,('s,'c,'k) pass) channel, ('s,'t,'k) channel, 'q, 'r) idx -> 
  ('c, empty, 'p, 'q) idx ->
  ('p,'r,unit) monad

val recv_slot :
  (('s,'t,('t,'c,'k) pass) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
  (empty, 'c, 'q, 'r) idx ->
  ('p,'r,unit) monad

val send_chan : 
  (('s,'t,('s,('ss,'tt,'kk)channel,'k) pass) channel, ('s,'t,'k) channel, 'q, 'r) idx -> 
  (('ss,'tt,'kk)channel, empty, 'p, 'q) idx ->
  ('p,'r,unit) monad

val recv_chan :
  (('s,'t,('t,('ss,'tt,'kk)channel,'k) pass) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
  (empty, ('ss,'tt,'kk)channel, 'q, 'r) idx ->
  ('p,'r,unit) monad

val send_new_chan : 
  (('s,'t,('s,('t,'s,'kk)channel,'k) pass) channel, ('s,'t,'k) channel, 'p, 'q) idx -> 
  (empty,('s,'t,'kk)channel, 'q, 'r) idx ->
  ('p,'r,unit) monad
               
val select_left :
  (('s,'t,('s,'k1,'k2)branch)channel, ('s,'t,'k1)channel, 'p, 'q) idx ->
  ('p,'q,unit) monad
val select_right :
  (('s,'t,('s,'k1,'k2)branch)channel, ('s,'t,'k2)channel, 'p, 'q) idx ->
  ('p,'q,unit) monad
val branch : 
  (('s,'t,('t,'k1,'k2)branch)channel, empty, 'p, 'q) idx ->
  (empty,('s,'t,'k1)channel, 'q,'q1) idx * (unit -> ('q1,'r,'a) monad) ->
  (empty,('s,'t,'k2)channel, 'q,'q2) idx * (unit -> ('q2,'r,'a) monad) ->
  ('p,'r,'a) monad

val fork : 
  (empty, (pos,neg,'k)channel, 'p, 'q) idx -> 
  (((neg,pos,'k)channel, all_empty) cons, all_empty, unit) monad -> 
  ('p,'q,unit) monad

module LinList : sig
  val nil : (empty,'a list,'p,'q) idx -> ('p,'q,unit) monad
  val put : ('a list,'a list,'q,'r) idx -> ('a,empty,'p,'q) idx -> ('p,'r,unit)monad
  val take : ('a list,'a list,'p,'p) idx * (empty,'a,'p,'q1) idx * (unit -> ('q1,'r,'b) monad) ->
             ('a list,empty,'p,'q2) idx * (unit -> ('q2,'r,'b) monad) ->
             ('p,'r,'b) monad
  (*val map : ('a list,'b list,'p,'q) idx -> ('c -> (('a,all_empty)cons,('b,all_empty)cons,'c)monad) -> 'c -> ('p,'q,'c) monad*)
end
               
module Routine : sig
  val send : 'v -> (('s,'t,('s,'v,'k)shot)channel, ('s,'t,'k) channel, unit) monad
  val recv : (('s,'t,('t,'v,'k)shot)channel, ('s,'t,'k) channel, 'v) monad
  val close : (('s,'t,finish)channel, empty, unit) monad
  val yield : 'v -> (('s,'t,('s,'t,'v,'w,'k)yield)channel, ('s,'t,'k)channel, 'w) monad
end

val run_routine :
  (empty, (pos,neg,'k)channel, 'p, 'q) idx ->
  ((neg,pos,'k)channel, empty, unit) monad ->
  ('p,'q,unit) monad
