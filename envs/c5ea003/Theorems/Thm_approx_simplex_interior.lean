-- Prove2me | Theorems.Thm_approx_simplex_interior
-- name    : approx_simplex_interior
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:29:17.453773+00:00
-- url     : https://prove2.me/theorems/e8203e40-a2e3-4d2c-a1d2-d81056694b06
-- title:
--   Approx simplex interior
-- statement:
--   Formal statement of `approx_simplex_interior` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem approx_simplex_interior    {A : Set C(X, ℝ)} {m : ℕ} (hm : 0 < m)
--       (hA : ∀ f : C(X, ℝ), f ∈ closure A)
--       {F : C(X, Fin m → ℝ)}
--       (hF : ∀ x, F x ∈ stdSimplex ℝ (Fin m))
--       (hpos : ∀ x i, 0 < F x i) :
--       F ∈ closure {G | ∃ H ∈ CoupledVecClass A m, G = (softmaxMap m hm).comp H} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HilbertSpace/VectorStoneWeierstrass.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HilbertSpace/VectorStoneWeierstrass.lean#L258

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

/-
**ε-approximation form.**
-/


/-! ## Coupled Vector Class -/


/-
`VecClass A m ⊆ CoupledVecClass A m`: use identity readout with `k = m`.
-/


/-
Closure under continuous output postcomposition.
-/

/-! ## Retraction onto Compact Targets -/

/-
Density into a compact target `K` via a continuous retraction `r`.
    If `r` fixes `K` pointwise and maps everything into `K`, and `F` maps into `K`,
    then `F` can be approximated by coupled-class maps that also map into `K`.
-/

/-! ## Simplex and Softmax -/


/-
Softmax output lies in the standard simplex.
-/

/-
Interior-simplex density: strictly positive simplex-valued maps can be
    approximated by softmax-composed coupled-class maps.
-/
omit [T2Space X] in

theorem approx_simplex_interior    {A : Set C(X, ℝ)} {m : ℕ} (hm : 0 < m)
    (hA : ∀ f : C(X, ℝ), f ∈ closure A)
    {F : C(X, Fin m → ℝ)}
    (hF : ∀ x, F x ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ x i, 0 < F x i) :
    F ∈ closure {G | ∃ H ∈ CoupledVecClass A m, G = (softmaxMap m hm).comp H} := by sorry
