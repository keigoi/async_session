include Session;;

let p () = 
  send _0 1234 >>
  recv _0 >>= fun str ->
  print_endline str;
  close _0 >>
  ret ()
      
      (*
val p :
    unit ->
      ((('a, 'b, ('a, int, ('b, string, finish) shot) shot) chan, 'c) cons,
          (empty, 'c) cons, unit)
          monad = <fun>
       *)
(*
val p :
  unit ->
  (((int, (string, 'a) recv) send, 'b) cons, ('a, 'b) cons, unit) monad
*)

let q () =
  recv _0 >>= fun i ->
  send _0 (string_of_int (i*2)) >>
  close _0 >>
  ret ()
(*
val q :
    unit ->
      ((('a, 'b, ('b, int, ('a, string, finish) shot) shot) chan, 'c) cons,
          (empty, 'c) cons, unit)
          monad
*)

let r () = 
  fork _0 (q ()) >>
  p ()
(*
val r :
    unit ->
      ((empty, (empty, 'a) cons) cons, (empty, (empty, 'a) cons) cons, unit)
          monad
*)

let _ = run (r())

(* output:

2468

 *)

            
let p2 () = 
  send _0 7777 >>
  recv_slot _0 _1 >>
  recv _1 >>= fun str ->
  print_endline str;
  close _0 >>
  close _1

let q2 () =
  recv _0 >>= fun v ->
  send_new_chan _0 _1 >>
  send _1 (string_of_int (v - 1111)) >>
  close _0 >>
  close _1

let r2 () =
  fork _0 (q2 ()) >>
  p2 ()

let _ = run (r2())

(* output:

6666

 *)

let rec p3 n =
    if n>10 then 
      select_right _0 >> close _0
    else
      select_left _0 >>
        send _0 n >>
        recv _0 >>= fun str ->
        print_endline str;
        p3 (n+1)

let rec q3 () = 
  branch _0
    (_0,recv _0 >>= fun x ->
        send _0 (string_of_int x) >>
        q3 ())
    (_0,close _0)

let r3 () =
  fork _0 (q3 ()) >>
  p3 1

let _ = run (r3 ())

(* output:

1
2
3
4
5
6
7
8
9
10

 *)

let r4 () =
  run_routine
    _0
    Routine.(send "Hello, " >> recv >>= fun x -> print_endline x; close) >>
  recv _0 >>= fun x ->
  send _0 (x ^ "World!") >>
  close _0

let _ = run (r4 ())        
(* output:

Hello, World!

 *)        
let _ = Async.Std.Scheduler.go()
