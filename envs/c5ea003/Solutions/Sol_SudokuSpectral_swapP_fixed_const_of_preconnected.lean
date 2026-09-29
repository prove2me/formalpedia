-- Prove2me | solution 1 for SudokuSpectral.swapP_fixed_const_of_preconnected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:54:46.70206+00:00
-- url     : https://prove2.me/submissions/3160b6b9-a9d3-4ace-8f48-b0ff12d2010b

-- Sol generated from Probability/SudokuSpectralGap.lean
import Mathlib
import Definitions.Def_Probability_SudokuSpectralGap
import Theorems.Thm_SudokuSpectral_swapP_harmonic_iff
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Spectral Gap of a Constraint-Satisfaction Swap Chain

A *constraint-satisfaction puzzle* (of which Sudoku is the archetypal example) is
solved by a large collection of admissible completions.  A natural way to sample a
random completion is the **swap chain**: from a current completion, repeatedly pick
a *compatible swap* — a local move that exchanges two entries while preserving every
constraint — and follow it with some holding probability.  The mixing speed of this
chain is governed by its **spectral gap** `1 - λ₂`, the distance between the top
eigenvalue `1` and the second eigenvalue.

This file builds the swap chain from first principles as a symmetric, doubly
stochastic transition matrix attached to an arbitrary finite graph `G` of admissible
moves, and isolates the *exact* dictionary between the algebra of the chain and the
combinatorics of `G`:

* the chain is **stochastic** and **symmetric** (`swapP_row_sum`, `swapP_symm`),
  hence the uniform distribution is stationary and the constant vector is a
  top eigenvector (`swapP_mulVec_one`);
* a vector is fixed by the chain **iff** it satisfies a discrete mean-value
  property (`swapP_harmonic_iff`);
* **reducibility ⇒ vanishing gap**: if the move graph is disconnected, there is a
  *nonconstant* fixed vector, so the eigenvalue `1` is degenerate and the gap is
  `0` (`swapP_reducible_nonconstant_fixed`);
* **irreducibility ⇒ simple top eigenvalue**: if the move graph is connected, every
  fixed vector is constant — a discrete maximum principle
  (`swapP_fixed_const_of_preconnected`);
* an explicit two-state computation exhibits the second eigenvalue `1 - 2c` and the
  strictly positive gap `2c` in the connected case
  (`twoState_eigenvector`, `twoState_gap_pos`), versus the identically-degenerate
  gap of the disconnected case (`twoState_bot_eq_one`).

The upshot corrects a tempting but false folklore slogan.  The gap is **not** a
function of the number of clues or of the number of completions: two puzzles with
the same number of completions can have gap `2c > 0` or gap `0` depending only on
whether the graph of compatible swaps is connected.  Connectivity of the move graph,
not clue count, is the true order parameter.

A genuine Sudoku fixture (`sudoku_row_sum`) shows that a single compatible swap
inside a row preserves the row's value multiset, hence keeps the chain inside one
level set — the combinatorial reason the swap graph decomposes into invariant blocks.
-/

open scoped BigOperators
open Matrix

open SudokuSpectral

variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ)







variable (G : SimpleGraph V)




variable [DecidableRel G.Adj] (c : ℝ)



variable (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ)











/-!
-- !-- Lab Notes -- !--

**Hypothesis.**  The circulating slogan says the "spectral gap of a Sudoku puzzle"
falls off a cliff at a critical clue density `d_c = 17/81`, with gap `> ε` below it,
gap `≈ 0` at it, and gap `= 0` (absorbing chain) above `30/81`.  We test the sharper
structural claim that a *single scalar* — the clue count — controls the gap.

**Experiment.**  We modelled the swap chain intrinsically: its state space is the set
of admissible completions, its moves are compatible swaps, and its transition matrix
`swapP G c` is the symmetric, doubly stochastic walk on the resulting move graph `G`.
The expansion `swapP_mulVec_apply` reduces one step of the chain to a discrete
Laplacian, from which the whole spectral dictionary follows.

**Analysis.**  The clue-density story is *false as stated* but points at a true
theorem once the order parameter is corrected.  What survives:
* `swapP_reducible_nonconstant_fixed` — a disconnected move graph forces `λ₂ = 1`,
  hence gap `0`.  This is the genuine "absorbing / no mixing" regime, but it is
  triggered by disconnection of the swap graph, *not* by having many clues.  (It
  needs no assumption on the holding rate `c` at all.)
* `swapP_fixed_const_of_preconnected` — a connected move graph makes `1` a simple
  eigenvalue (the discrete maximum principle), the prerequisite for a positive gap.
* `twoState_eigenvector` / `twoState_gap_pos` versus `twoState_bot_eq_one` — an
  explicit pair of two-completion puzzles with identical clue/solution counts and
  gaps `2c > 0` and `0` respectively.  This *directly refutes* "gap is a function of
  clue count."
* `sudoku_row_sum` — why the move graph splits into blocks at all: compatible swaps
  conserve each row's value multiset.

**Critique.**  None of the results is `native_decide`/definitional: the reducibility
and irreducibility theorems use component indicators and a genuine maximum-principle
argument; the two-state gap uses an explicit eigenvector computation.  The corrected
claim is guarded — `swapP_fixed_const_of_preconnected` gives only simplicity of `1`
(a necessary condition for a positive gap), and the *quantitative* positive gap is
proved only in the exactly-solvable two-state model, honestly bounding the scope.

**Synthesis.**  Connectivity of the graph of compatible swaps, not clue count, is the
order parameter for mixing.  The "phase transition" is the reducible/irreducible
dichotomy of the swap graph.
-/


open SudokuSpectral in
theorem solution(hc : c ≠ 0) (hconn : G.Preconnected)
    (f : V → ℝ) (hf : (swapP G c).mulVec f = f) : ∀ a b, f a = f b := by
  rw [swapP_harmonic_iff G c hc] at hf
  rcases isEmpty_or_nonempty V with hV | hV
  · intro a; exact (IsEmpty.false a).elim
  · obtain ⟨xM, hM⟩ := Finite.exists_max f
    set M := f xM with hMdef
    have step : ∀ x, f x = M → ∀ z, G.Adj x z → f z = M := by
      intro x hx z hxz
      have hmvp := hf x
      have hsumM : (∑ y ∈ G.neighborFinset x, f y) = G.degree x * M := by rw [hmvp, hx]
      have hconstM : (∑ _y ∈ G.neighborFinset x, M) = G.degree x * M := by
        rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
      have hnn : ∀ y ∈ G.neighborFinset x, 0 ≤ M - f y := by
        intro y _; linarith [hM y]
      have hzero : (∑ y ∈ G.neighborFinset x, (M - f y)) = 0 := by
        rw [Finset.sum_sub_distrib, hsumM, hconstM]; ring
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero
      have hz : M - f z = 0 := hall z (by rw [SimpleGraph.mem_neighborFinset]; exact hxz)
      linarith
    have prop : ∀ a z, G.Walk a z → f a = M → f z = M := by
      intro a z w
      induction w with
      | nil => intro h; exact h
      | cons hadj w' ih => intro h; exact ih (step _ h _ hadj)
    have hallM : ∀ z, f z = M := by
      intro z
      obtain ⟨w⟩ := hconn xM z
      exact prop xM z w rfl
    intro a b; rw [hallM a, hallM b]
