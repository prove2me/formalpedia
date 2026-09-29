-- Prove2me | solution 1 for AdjSum.adjMat_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:10:04.451046+00:00
-- url     : https://prove2.me/submissions/843049cb-78de-48d2-8112-31c1035e32fb

-- Sol generated from Applications/AdjacentSumPolytopes/Basic.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic

/-!
# Adjacent-sum lattice sets and their transfer matrices

Fix a *slack* parameter `s : ℕ`.  The **open adjacent-sum set** in dimension `d + 1`
is the set of lattice points

`Δ(s, d) = { x ∈ ℤ^{d+1} : 0 ≤ xᵢ,  xᵢ + xᵢ₊₁ ≤ s  (0 ≤ i < d) }`

and the **cyclic adjacent-sum set** is the analogous set where the index `i + 1` is
taken modulo the length, so that the constraint graph is a cycle rather than a path.
Both are the sets of lattice points of a lattice polytope (the `d`-fold "adjacent-sum"
polytope), which is why their counting functions are Ehrhart-type quantities.

Because `0 ≤ xᵢ` and `xᵢ + xᵢ₊₁ ≤ s` force `xᵢ ≤ s`, every coordinate lives in the
`(s+1)`-element state space `Fin (s+1)`; the model with `s + 1` slack has the
`(s + 2)`-state transfer matrix `adjMat (s+1)`.

The **transfer matrix** is the `(s+1) × (s+1)` `0/1` matrix

`adjMat s a b = 1 ↔ a + b ≤ s`.

## Main results

* `AdjSum.card_pathSet` : the number of open adjacent-sum points of length `d + 1`
  with prescribed first coordinate `a` and last coordinate `b` is the matrix entry
  `(adjMat s ^ d) a b`.
* `AdjSum.card_openSet` : the total number of open points of length `d+1` is the
  sum of all entries of `adjMat s ^ d`.
* `AdjSum.card_cycSet` : the number of cyclic points of length `d + 1` is
  `trace (adjMat s ^ (d+1))`.
* `AdjSum.adjMat_isSymm`, `AdjSum.card_openSet_symm_swap` : structural symmetries.

-- !-- Lab Notes -- !--
* **Hypothesis.** The naive "walks in a digraph" heuristic should hold verbatim
  for these lattice sets: open points ↔ matrix products, cyclic points ↔ traces.
* **Experiment.** `#eval`-ing `trace (adjMat 1 ^ n)` gives `1, 3, 4, 7, 11, 18, 29, 47`
  (Lucas numbers) and `∑ₐ∑_b (adjMat 1 ^ n) a b` gives `2, 3, 5, 8, 13, 21, 34`
  (Fibonacci), matching a direct enumeration of `0/1` vectors with no two adjacent
  ones — the classical sanity check.  For `s = 2`: cyclic `2, 6, 11, 26, 57, 129`,
  open `3, 6, 14, 31, 70, 157`.
* **Analysis.** The proofs are genuine `Fin.snoc`/`Fin.init` bijections; the cyclic
  case additionally needs the wrap-around index lemma `castSucc_add_one` and
  `Fin.last_add_one`.
* **Critique.** No statement here is definitional: both sides are computed by
  different mechanisms (cardinality of a filtered `Finset` vs. matrix powers), and
  the induction step is a fiberwise decomposition, not `rfl`.
-/

open AdjSum

open Finset Matrix










/-! ### Index bookkeeping for the cyclic wrap-around -/






/-! ### The transfer-matrix bijections -/






open AdjSum in
lemma adjMat_apply (s : ℕ) (a b : Fin (s + 1)) :
    adjMat s a b = if (a : ℕ) + (b : ℕ) ≤ s then 1 else 0 := rfl

open AdjSum in
theorem solution(s : ℕ) : (adjMat s).IsSymm := by
  ext a b
  simp only [Matrix.transpose_apply, adjMat_apply]
  rw [Nat.add_comm]
