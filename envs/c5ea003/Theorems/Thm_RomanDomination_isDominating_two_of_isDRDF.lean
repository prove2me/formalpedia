-- Prove2me | Theorems.Thm_RomanDomination_isDominating_two_of_isDRDF
-- name    : RomanDomination.isDominating_two_of_isDRDF
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:45:20.852738+00:00
-- url     : https://prove2.me/theorems/fc2f5949-1ac9-4a06-8c86-079513b7fc9e
-- title:
--   The vertices labelled at least `2` by a double Roman dominating function
-- statement:
--   The vertices labelled at least `2` by a double Roman dominating function
--   form a dominating set.
--
--   ```lean
--   theorem RomanDomination.isDominating_two_of_isDRDF{f : V → ℕ} (h : IsDRDF G f) :
--       IsDominating G (Finset.univ.filter fun v => 2 ≤ f v) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/Variants.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/Variants.lean#L372

-- Thm stub generated from Geometry/RomanDomination/Variants.lean
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







omit [DecidableEq V] [DecidableRel G.Adj] in

theorem RomanDomination.isDominating_two_of_isDRDF{f : V → ℕ} (h : IsDRDF G f) :
    IsDominating G (Finset.univ.filter fun v => 2 ≤ f v) := by sorry
