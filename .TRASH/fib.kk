import std/num/int32

// 1. Non-tail recursion (needs div, emits FIP warning on non-tail call)
fun bad-fact(n : int) : div int
  if n <= 0 then 1 else n * bad-fact(n - 1)

// 2. Tail-recursive inner helper (tail verifies loop is tail-recursive)
fun fact-tail(n : int) : div int
  tail fun loop(i : int, acc : int) : div int
    if i <= 0 then acc
    else loop(i - 1, i * acc)
  loop(n, 1)

// 3 & 4. True FIP tail recursion (fully passes FIP analysis!)
fip fun fact-acc(n : int32, acc : int32) : div int32
  if n <= 0.int32 then acc
  else fact-acc(n - 1.int32, n * acc)

fip fun fact-fip(n : int32) : div int32
  fact-acc(n, 1.int32)

// 5. Imperative while loop (valid Koka, but cannot be FIP due to var/closures)
fun fact-while(n : int) : div int
  var acc := 1
  var i   := n
  while { i > 0 }
    acc := acc * i
    i   := i - 1
  acc

fun main()
  println("bad-fact(2)   = " ++ bad-fact(2).show)
  println("fact-tail(5)  = " ++ fact-tail(5).show)
  println("fact-fip(5)   = " ++ fact-fip(5.int32).show)
  println("fact-while(5) = " ++ fact-while(5).show)
