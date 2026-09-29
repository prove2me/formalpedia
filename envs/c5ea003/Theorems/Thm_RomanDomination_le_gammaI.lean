-- Prove2me | Theorems.Thm_RomanDomination_le_gammaI
-- name    : RomanDomination.le_gammaI
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:15.400894+00:00
-- url     : https://prove2.me/theorems/b9c145f8-1e4d-4346-8347-a6d5e4dd3997
-- title:
--   Lower bounds on `γ_I` are proved by bounding the weight of every Italian
-- statement:
--   Lower bounds on `γ_I` are proved by bounding the weight of every Italian
--   dominating function.
--
--   ```lean
--   theorem RomanDomination.le_gammaI{k : ℕ} (h : ∀ f : V → ℕ, IsIDF G f → k ≤ weight f) : k ≤ gammaI G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/Variants.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/Variants.lean#L198

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














omit [DecidableEq V] in

theorem RomanDomination.le_gammaI{k : ℕ} (h : ∀ f : V → ℕ, IsIDF G f → k ≤ weight f) : k ≤ gammaI G := by sorry
