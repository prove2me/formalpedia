-- Prove2me | solution 1 for RomanDomination.le_gammaR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:45:27.584326+00:00
-- url     : https://prove2.me/submissions/ce5b7f58-259a-4bbd-b376-ccff8aea93b3

-- Sol generated from Geometry/RomanDomination/Variants.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_isPRDF_of_isURRDF
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
/-- The constant labelling `1` is a unique response Roman dominating function. -/
lemma isURRDF_one : IsURRDF G (fun _ : V => 1) := by
  refine ⟨fun _ => by norm_num, fun v hv => by simp at hv, fun v _ u _ => by norm_num⟩


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma isRDF_of_isPRDF {f : V → ℕ} (h : IsPRDF G f) : IsRDF G f :=
  ⟨h.1, fun v hv => (h.2 v hv).imp fun _ hu => hu.1⟩




/-! ### Membership and minimality plumbing -/








omit [DecidableEq V] [DecidableRel G.Adj] in
lemma exists_gammaR : ∃ f : V → ℕ, IsRDF G f ∧ weight f = gammaR G :=
  Nat.sInf_mem (s := {w | ∃ f, IsRDF G f ∧ weight f = w})
    ⟨weight (fun _ : V => 1), fun _ => 1,
      isRDF_of_isPRDF G (isPRDF_of_isURRDF G (isURRDF_one G)), rfl⟩








/-! ### Elementary weight computations -/


variable (f : V → ℕ) (S : Finset V)








/-! ### Transfer constructions between the variants -/


variable (G : SimpleGraph V) [DecidableRel G.Adj]









/-! ### The chain of inequalities -/


variable (G : SimpleGraph V) [DecidableRel G.Adj]















variable (G : SimpleGraph V) [DecidableRel G.Adj]







open RomanDomination in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem solution{k : ℕ} (h : ∀ f : V → ℕ, IsRDF G f → k ≤ weight f) : k ≤ gammaR G := by
  obtain ⟨f, hf, hw⟩ := exists_gammaR G
  exact hw ▸ h f hf
