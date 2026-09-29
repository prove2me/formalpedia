-- Prove2me | solution 1 for RomanDomination.isDRDF_succ_support
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:20.066801+00:00
-- url     : https://prove2.me/submissions/1f1b2f9f-056c-400f-bf94-d0ca1e1ffe0c

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
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem solution{f : V → ℕ} (h : IsRDF G f) :
    IsDRDF G (fun v => if f v = 0 then 0 else f v + 1) := by
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · -- g v ≤ 3
    by_cases hf : f v = 0
    · simp [hf]
    · have := h.1 v
      simp [hf]
      omega
  · -- g v = 0 case
    simp at hv
    have := h.2 v hv
    obtain ⟨u, hadj, hu⟩ := this
    left
    use u, hadj
    simp [hu]
  · -- g v = 1 case
    by_cases hfv : f v = 0 <;> simp [hfv] at hv
