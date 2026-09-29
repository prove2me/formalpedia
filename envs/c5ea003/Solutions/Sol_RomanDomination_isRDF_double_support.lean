-- Prove2me | solution 1 for RomanDomination.isRDF_double_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:36.777767+00:00
-- url     : https://prove2.me/submissions/66da86ce-3c12-4cdf-b77f-98f305b95c20

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
    IsRDF G (fun v => if 1 ≤ f v then 2 else 0) := by
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · simp only; split_ifs <;> norm_num
  · by_cases hv0 : f v = 0
    · have hsum := h.2 v hv0
      by_contra hne
      push_neg at hne
      have : ∑ u ∈ G.neighborFinset v, f u = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        simp_all [SimpleGraph.mem_neighborFinset]
      omega
    · simp_all
