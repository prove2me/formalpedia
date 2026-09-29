-- Prove2me | Definitions.Def_Applications_PosetTheory_StackSortingDepth
-- name    : Applications_PosetTheory_StackSortingDepth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:32.278226+00:00
-- url     : https://prove2.me/theorems/1c073df5-67e5-4846-93d7-eeb88ecf1be2
-- title:
--   Aether Catalog definitions — Applications_PosetTheory_StackSortingDepth
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PosetTheory.StackSortingDepth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PosetTheory/StackSortingDepth.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Stack-sorting depth of permutations

This file develops West's **stack-sorting map** `stackSort` on lists of natural
numbers, together with the associated notion of **stack-sorting depth**: the
minimal number of times the map must be iterated to reach the sorted list.

## Main definitions

* `stackSort`     — one pass of West's stack-sorting operator, implemented by a
  left-to-right stack simulation (`sortPass` / `popLess`).
* `depth`         — the least `t` with `stackSort^[t] l` equal to the sorted
  list (computed by a bounded search `depthAux`; the bound `l.length` is always
  large enough).
* `permsN n`      — all permutations of `[1, 2, …, n]`.
* `depthDist n`   — the depth distribution: for each value `t`, the number of
  permutations of `[1, …, n]` of stack-sorting depth `t`.

## Main results

* `stackSort_perm`            — `stackSort l` is a permutation of `l`.
* `stackSort_length`          — `stackSort` preserves length.
* `stackSort_strictSorted_eq` — a strictly increasing list is a fixed point of
  `stackSort`.
* `depth_sorted`              — an (ascending-)sorted list has depth `0`.
* `permsN_complete`           — `permsN n` lists exactly the permutations of
  `[1, …, n]`.
* `depthLe1_card_eq_catalan_*`— the number of permutations of `[1, …, n]` of
  depth at most `1` (the one-pass stack-sortable permutations) equals the
  Catalan number `Cₙ`, verified for `n ≤ 6`.

These four core lemmas are independent: `stackSort_length` is derived from
`stackSort_perm`, but neither `stackSort_strictSorted_eq` nor `depth_sorted`
depends on the permutation lemmas, so there is no circular dependency.
-/


namespace StackSortingDepth

/-! ## West's stack-sorting map -/

/-- `popLess x stack` pops off the top of `stack` (whose head is the top) every
element that is strictly smaller than `x`, returning the popped elements (in pop
order) together with the remaining stack. -/
def popLess (x : ℕ) : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | (t :: ts) =>
      if t < x then
        (fun p => (t :: p.1, p.2)) (popLess x ts)
      else
        ([], t :: ts)

/-- One left-to-right pass of West's stack-sorting algorithm.  `sortPass xs
stack` processes the remaining input `xs` against the current `stack`: for each
new symbol it first flushes every smaller stack element to the output, then
pushes the symbol; when the input is exhausted the whole stack is flushed. -/
def sortPass : List ℕ → List ℕ → List ℕ
  | [], stack => stack
  | (x :: xs), stack =>
      let p := popLess x stack
      p.1 ++ sortPass xs (x :: p.2)

/-- West's stack-sorting map: one full pass starting from an empty stack. -/
def stackSort (l : List ℕ) : List ℕ := sortPass l []

/-! ## Permutation and length invariants -/





/-! ## Strictly sorted lists are fixed points -/



/-! ## Stack-sorting depth -/

/-- Bounded search underlying `depth`: starting from `cur`, count how many
applications of `stackSort` are needed to reach `target`, giving up after `fuel`
steps. -/
def depthAux (target : List ℕ) : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | cur, (f + 1) => if cur = target then 0 else 1 + depthAux target (stackSort cur) f

/-- The stack-sorting depth of `l`: the least `t` such that iterating `stackSort`
`t` times turns `l` into its ascending sort.  The search bound `l.length` always
suffices. -/
def depth (l : List ℕ) : ℕ := depthAux (l.mergeSort (· ≤ ·)) l l.length


/-! ## Enumerating permutations -/

/-- All permutations of `[1, 2, …, n]`. -/
def permsN (n : ℕ) : List (List ℕ) := (List.range' 1 n).permutations


/-! ## Depth distribution and the Catalan law

The number of permutations of `[1, …, n]` of stack-sorting depth `0` or `1`
(i.e. sortable in a single pass) is the Catalan number `Cₙ`.  We record this
"Catalan law" for `n ≤ 6` together with the full depth distribution. -/


-- Depth distributions for small `n` (matching OEIS data):
--   n=1: [(0,1)]
--   n=2: [(0,1),(1,1)]
--   n=3: [(0,1),(1,4),(2,1)]
--   n=4: [(0,1),(1,13),(2,8),(3,2)]
--   n=5: [(0,1),(1,41),(2,49),(3,23),(4,6)]
--   n=6: [(0,1),(1,131),(2,276),(3,198),(4,90),(5,24)]
/-- Number of one-pass stack-sortable permutations of `[1, …, n]`. -/
def stackSortableCount (n : ℕ) : ℕ := ((permsN n).filter (fun p => depth p ≤ 1)).length




end StackSortingDepth


