-- Prove2me | Theorems.Thm_closure_vecClass_eq_univ_of_scalar
-- name    : closure_vecClass_eq_univ_of_scalar
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:29:10.701983+00:00
-- url     : https://prove2.me/theorems/3fb01b88-c188-43f8-8072-9acf51ca25f7
-- title:
--   Closure vecClass eq univ of scalar
-- statement:
--   Formal statement of `closure_vecClass_eq_univ_of_scalar` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem closure_vecClass_eq_univ_of_scalar    {A : Set C(X, ℝ)} {m : ℕ}
--       (hA : ∀ f : C(X, ℝ), f ∈ closure A) :
--       ∀ F : C(X, Fin m → ℝ), F ∈ closure (VecClass A m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HilbertSpace/VectorStoneWeierstrass.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HilbertSpace/VectorStoneWeierstrass.lean#L104

-- Thm stub generated from Bridges/HilbertSpace/VectorStoneWeierstrass.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_VectorStoneWeierstrass
/-
# Vector-Valued EML Stone–Weierstrass Theorem

This file lifts the scalar Stone–Weierstrass density theorem from `C(X, ℝ)` to
finite-dimensional vector-valued codomains `C(X, Fin m → ℝ)`.

## Main definitions

* `coordMap i` — the `i`-th coordinate projection as a continuous map
* `VecClass A m` — the coordinatewise vector class attached to a scalar class `A`
* `CoupledVecClass A m` — shared-feature class with continuous output coupling

## Main results

* `closure_vecClass_eq_univ_of_scalar` — if `A` is dense in `C(X, ℝ)`, then
  `VecClass A m` is dense in `C(X, Fin m → ℝ)`
* `exists_mem_vecClass_uniformApprox` — ε-approximation form
* `dense_coupledVecClass_of_dense_scalar` — density of the coupled class
* `comp_mem_coupledVecClass` — closure under continuous output postcomposition
* `dense_into_compactRange_of_retraction` — density with retraction onto compact target
* `softmaxMap_mem_stdSimplex` — softmax maps into the standard simplex
* `eml_vec_stoneWeierstrass` — EML specialization

## Mathematical significance

This development upgrades scalar EML universality into a genuinely usable
vector-valued approximation theory, providing the formal bridge from scalar
universality to multiclass classifiers, controllers, and constrained outputs.
-/

noncomputable section

open ContinuousMap Set Topology Real

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Core Definitions -/








/-! ## Coordinatewise Norm Estimates -/

/-
Pointwise bound: if every coordinate is bounded by `δ`, then the pi-norm
    (which is the sup norm on `Fin m → ℝ`) is bounded by `δ`.
-/


/-! ## Main Density Theorem -/

/-
**Coordinatewise density in `C(X, Fin m → ℝ)`.**
    If the scalar class `A` is dense in `C(X, ℝ)`, then every vector-valued
    function is in the closure of `VecClass A m`.
-/
omit [T2Space X] in

theorem closure_vecClass_eq_univ_of_scalar    {A : Set C(X, ℝ)} {m : ℕ}
    (hA : ∀ f : C(X, ℝ), f ∈ closure A) :
    ∀ F : C(X, Fin m → ℝ), F ∈ closure (VecClass A m) := by sorry
