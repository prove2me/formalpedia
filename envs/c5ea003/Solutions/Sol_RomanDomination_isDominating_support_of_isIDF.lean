-- Prove2me | solution 1 for RomanDomination.isDominating_support_of_isIDF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:20.801275+00:00
-- url     : https://prove2.me/submissions/fc8d646e-583e-4c79-9360-98d276c9ab1a

-- Sol generated from Geometry/RomanDomination/Variants.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_Variants
/-
# Roman-type domination parameters and the inequality chain

This file develops, from scratch, the family of *Roman-type domination* parameters
studied in the literature on Roman domination and its variants:

* the **domination number** `gammaDom G`,
* the **Roman domination number** `gammaR G`,
* the **Italian (a.k.a. Roman-{2}) domination number** `gammaI G`,
* the **double Roman domination number** `gammaDR G`,
* the **perfect Roman domination number** `gammaPR G`,
* the **unique response Roman domination number** `gammaUR G`.

All of them are defined as an infimum of the weight `∑ v, f v` over a class of
functions `f : V → ℕ` satisfying a local protection condition, and all of them are
well defined (the defining set of weights is non-empty) for every finite graph.

The main results are the classical comparison inequalities relating these six
parameters, together with the general upper bound `γ_R(G) ≤ n` and the exact value
`γ_R(G) = n` for the edgeless graph.
-/


open RomanDomination

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]



variable (G : SimpleGraph V) [DecidableRel G.Adj]















variable (G : SimpleGraph V) [DecidableRel G.Adj]









/-! ### Membership and minimality plumbing -/
















/-! ### Elementary weight computations -/


variable (f : V → ℕ) (S : Finset V)








/-! ### Transfer constructions between the variants -/


variable (G : SimpleGraph V) [DecidableRel G.Adj]









/-! ### The chain of inequalities -/


variable (G : SimpleGraph V) [DecidableRel G.Adj]















variable (G : SimpleGraph V) [DecidableRel G.Adj]







open RomanDomination in
omit [DecidableEq V] in
theorem solution{f : V → ℕ} (h : IsIDF G f) :
    IsDominating G (Finset.univ.filter fun v => 1 ≤ f v) := by
  intro v
  by_cases hv : f v = 0
  · right
    have hsum := h.2 v hv
    by_contra hne
    push_neg at hne
    have : ∑ u ∈ G.neighborFinset v, f u = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [SimpleGraph.mem_neighborFinset] at hu
      by_contra hfpos
      push_neg at hfpos
      have hfpos' : 1 ≤ f u := Nat.one_le_iff_ne_zero.mpr hfpos
      exact hne u (by simpa using hfpos') hu
    omega
  · left
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.pos_of_ne_zero hv
