module

public import RequestProject.Frontend.Util

@[expose] public section

/- ══════════════════ PAPER sec. 4.2, App. A.3 START: Sorting lists in-place; Quick Sort (PDF pp. 20-21; App. A.3 on pp. 35-36) ══════════════════
   The fully in-place quicksort and the simpler `fbip` variant. -/

/-!
# Appendix A.3: quicksort

The fully in-place quicksort of Section 4.2 / Appendix A.3, verbatim, together with the
`fbip` quicksort of Section 4.2 (which is functional but in-place, but not fully
in-place since its stack usage is unbounded).  `from-list` takes two untyped parameters
`x, y` as in the paper.
-/

namespace Examples.QuickSort

open Koka FIP

/-- Appendix A.3: fully in-place quicksort. -/
def quicksort : FipModule := [KOKA_FIP|
import std/num/int32
import std/os/env

alias elem = int32

ref type pad
  Pad

ref type unit2
  Unit2(a : pad, b : pad)

type maybe2<a>
  Nothing2
  Just2(a : a, b : pad)

type sublist<a>
  SCons(a : a, cs : sublist<a>)
  STuple(a : a, b : a)

type partition<a>
  Sublist(c : sublist<a>, bdl : partition<a>)
  Singleton(c : a, bdl : partition<a>)
  End

fip fun from-list(x, y, u : unit2, xs : list<elem>) : sublist<elem>
  match xs
    Cons(z, zs) -> SCons(x, from-list(y, z, u, zs))
    Nil -> STuple(x, y)

fip fun to-bundle(xs : list<elem>, bdl' : partition<elem>) : partition<elem>
  match xs
    Cons(x, Cons(y, xs)) -> Sublist(from-list(x, y, Unit2(Pad, Pad), xs), bdl')
    Cons(x, Nil) -> Singleton(x, bdl')
    Nil -> bdl'

fip fun quicksort(xs : list<elem>) : div list<elem>
  quicksort-go(to-bundle(xs, End))

fip fun quicksort-go(bdl : partition<elem>) : div list<elem>
  match bdl
    Sublist(xs, bdl') -> match xs
      SCons(p, xs) ->
        val (lo, hi) = partition(p, xs, Unit2(Pad, Pad))
        quicksort-go(to-bundle(lo, Singleton(p, to-bundle(hi, bdl'))))
      STuple(x, y) | x <= y -> Cons(x, Cons(y, quicksort-go(bdl')))
                   | _      -> Cons(y, Cons(x, quicksort-go(bdl')))
    Singleton(p, b) -> Cons(p, quicksort-go(b))
    End -> Nil

fip fun partition(^p : elem, xs : sublist<elem>, u : unit2) : (list<elem>, list<elem>)
  match(xs)
    SCons(x, xx) -> if p <= x
      then
        val (lo, hi) = partition(p, xx, u)
        (lo, Cons(x, hi))
      else
        val (lo, hi) = partition(p, xx, u)
        (Cons(x, lo), hi)
    STuple(x, y) -> if p <= x
      then if p <= y
        then (Nil, Cons(x, Cons(y, Nil)))
        else (Cons(y, Nil), Cons(x, Nil))
      else if p <= y
        then (Cons(x, Nil), Cons(y, Nil))
        else (Cons(x, Cons(y, Nil)), Nil)
]

/-- All functions of Appendix A.3 are fully in-place. -/
theorem quicksort_wf : quicksort.sig.Wf := quicksort.wf

/-- Quicksort sorts `[5, 2, 8, 1, 9, 3, 7, 4, 6, 0]`. -/
theorem quicksort_example :
    (quicksort.run "quicksort" [] [listV [5, 2, 8, 1, 9, 3, 7, 4, 6, 0]] 100000).map
      (·.map ofListV) = some [some [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] := by
  decide +kernel

/-- Section 4.2: the usual functional-but-in-place quicksort (on `int` lists). -/
def fbipQuicksort : FipModule := [KOKA_FIP|
fbip fun split(^p : int, xs : list<int>) : (list<int>, list<int>)
  match! xs
    Cons(x, xx) ->
      val (lo, hi) = split(p, xx)
      if x < p then (Cons(x, lo), hi) else (lo, Cons(x, hi))
    Nil -> (Nil, Nil)

fbip fun append(xs : list<int>, ys : list<int>) : list<int>
  match! xs
    Cons(x, xx) -> Cons(x, append(xx, ys))
    Nil -> ys

fbip fun quicksort(xs : list<int>) : list<int>
  match! xs
    Nil -> Nil
    Cons(pivot, xx) ->
      val (lo, hi) = split(pivot, xx) // split xx into (lo,hi) in-place
      val (lo', hi') = (quicksort(lo), quicksort(hi)) // sort the sublists
      append(lo', Cons(pivot, hi'))
]

/-- The `fbip` quicksort is functional but in-place. -/
theorem fbipQuicksort_wf : fbipQuicksort.sig.Wf := fbipQuicksort.wf

/-- The `fbip` quicksort sorts. -/
theorem fbipQuicksort_example :
    (fbipQuicksort.run "quicksort" [] [listV [5, 2, 8, 1, 9, 3, 7, 4, 6, 0]] 100000).map
      (·.map ofListV) = some [some [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] := by
  decide +kernel

end Examples.QuickSort

/- ══════════════════ PAPER sec. 4.2, App. A.3 END: Sorting lists in-place; Quick Sort ══════════════════ -/
