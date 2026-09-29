-- Prove2me | Theorems.Thm_RomanDomination_isDRDF_succ_support
-- name    : RomanDomination.isDRDF_succ_support
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:45:13.925289+00:00
-- url     : https://prove2.me/theorems/81d051e8-8121-4e77-a1f1-3fa6932f23c7
-- title:
--   Adding one on the support of a Roman dominating function gives a double
-- statement:
--   Adding one on the support of a Roman dominating function gives a double
--   Roman dominating function.
--
--   ```lean
--   theorem RomanDomination.isDRDF_succ_support{f : V → ℕ} (h : IsRDF G f) :
--       IsDRDF G (fun v => if f v = 0 then 0 else f v + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/Variants.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/Variants.lean#L350

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






omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

theorem RomanDomination.isDRDF_succ_support{f : V → ℕ} (h : IsRDF G f) :
    IsDRDF G (fun v => if f v = 0 then 0 else f v + 1) := by sorry
