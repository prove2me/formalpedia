-- Prove2me | solution 1 for RomanDomination.gammaR_le_gammaPR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:17.58878+00:00
-- url     : https://prove2.me/submissions/8de94697-7052-4411-8a49-4069fceaa864

-- Sol generated from Geometry/RomanDomination/Variants.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_exists_gammaPR
import Theorems.Thm_RomanDomination_gammaR_le
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





omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isRDF_of_isPRDF {f : V → ℕ} (h : IsPRDF G f) : IsRDF G f :=
  ⟨h.1, fun v hv => (h.2 v hv).imp fun _ hu => hu.1⟩




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
theorem solution: gammaR G ≤ gammaPR G := by
  obtain ⟨f, hf, hw⟩ := exists_gammaPR G
  exact hw ▸ gammaR_le G (isRDF_of_isPRDF G hf)
