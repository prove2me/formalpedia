-- Prove2me | solution 1 for RomanDomination.isDominating_two_of_isDRDF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:25.95069+00:00
-- url     : https://prove2.me/submissions/a6623ed5-cbeb-40a1-93d8-e58aff044a1d

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
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem solution{f : V → ℕ} (h : IsDRDF G f) :
    IsDominating G (Finset.univ.filter fun v => 2 ≤ f v) := by
  intro v
  by_cases hv : 2 ≤ f v
  · left
    simp [hv]
  · right
    have hfv : f v = 0 ∨ f v = 1 := by omega
    cases hfv with
    | inl h0 =>
      have := h.2.1 v h0
      rcases this with ⟨u, hu, hu'⟩ | ⟨u, w, _, huv, hwv, hu'', hw''⟩
      · exact ⟨u, by simp [hu'], hu⟩
      · exact ⟨u, by simp [hu''], huv⟩
    | inr h1 =>
      exact (h.2.2 v h1).imp fun u hu => ⟨by simp [hu.2], hu.1⟩
