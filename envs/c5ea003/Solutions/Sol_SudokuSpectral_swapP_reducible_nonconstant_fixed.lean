-- Prove2me | solution 1 for SudokuSpectral.swapP_reducible_nonconstant_fixed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:56:00.566018+00:00
-- url     : https://prove2.me/submissions/94a7de0a-66f3-4d28-a6c8-6bc87d940023

-- Sol generated from Probability/SudokuSpectralGap.lean
import Mathlib
import Definitions.Def_Probability_SudokuSpectralGap
import Theorems.Thm_SudokuSpectral_swapP_mulVec_apply
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


-- open removed: section is not a namespace
theorem componentIndicator_of_reachable (x₀ y : V) (h : G.Reachable x₀ y) :
    componentIndicator G x₀ y = 1 := by simp [componentIndicator, h]

-- open removed: section is not a namespace
theorem componentIndicator_of_not_reachable (x₀ y : V) (h : ¬ G.Reachable x₀ y) :
    componentIndicator G x₀ y = 0 := by simp [componentIndicator, h]

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
-- open removed: section is not a namespace
theorem solution(hdis : ¬ G.Preconnected) :
    ∃ f : V → ℝ, (swapP G c).mulVec f = f ∧ ¬ (∀ a b, f a = f b) := by
  rw [SimpleGraph.Preconnected] at hdis
  push_neg at hdis
  obtain ⟨x₀, y₀, hxy⟩ := hdis
  refine ⟨componentIndicator G x₀, ?_, ?_⟩
  · funext x
    rw [swapP_mulVec_apply]
    have hmvp : (∑ y ∈ G.neighborFinset x, componentIndicator G x₀ y)
        = G.degree x * componentIndicator G x₀ x := by
      by_cases hx : G.Reachable x₀ x
      · rw [componentIndicator_of_reachable G x₀ x hx]
        have hcon : ∀ y ∈ G.neighborFinset x, componentIndicator G x₀ y = 1 := by
          intro y hy
          rw [SimpleGraph.mem_neighborFinset] at hy
          exact componentIndicator_of_reachable G x₀ y (hx.trans hy.reachable)
        rw [Finset.sum_congr rfl hcon, Finset.sum_const,
          SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
      · rw [componentIndicator_of_not_reachable G x₀ x hx]
        have hcon : ∀ y ∈ G.neighborFinset x, componentIndicator G x₀ y = 0 := by
          intro y hy
          rw [SimpleGraph.mem_neighborFinset] at hy
          exact componentIndicator_of_not_reachable G x₀ y
            (fun hr => hx (hr.trans hy.symm.reachable))
        rw [Finset.sum_congr rfl hcon, Finset.sum_const_zero, mul_zero]
    rw [hmvp]; ring
  · intro hconst
    have h0 : componentIndicator G x₀ x₀ = componentIndicator G x₀ y₀ := hconst _ _
    rw [componentIndicator_of_reachable G x₀ x₀ (SimpleGraph.Reachable.refl x₀),
      componentIndicator_of_not_reachable G x₀ y₀ hxy] at h0
    exact one_ne_zero h0
