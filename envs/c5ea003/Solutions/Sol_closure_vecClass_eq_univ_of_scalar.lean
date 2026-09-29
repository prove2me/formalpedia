-- Prove2me | solution 1 for closure_vecClass_eq_univ_of_scalar
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:58:54.613762+00:00
-- url     : https://prove2.me/submissions/2e7ccda3-82dd-4cae-9cf1-f034ba3f4083

-- Sol generated from Bridges/HilbertSpace/VectorStoneWeierstrass.lean
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






omit [CompactSpace X] [T2Space X] in
theorem coordMap_comp_assembleVec {m : ℕ} (g : Fin m → C(X, ℝ)) (i : Fin m) :
    (coordMap m i).comp (assembleVec g) = g i := by
  ext x; simp [coordMap, assembleVec]

omit [CompactSpace X] [T2Space X] in
theorem assembleVec_mem_vecClass {A : Set C(X, ℝ)} {m : ℕ}
    {g : Fin m → C(X, ℝ)} (hg : ∀ i, g i ∈ A) :
    assembleVec g ∈ VecClass A m := by
  intro i; rw [coordMap_comp_assembleVec]; exact hg i

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

/-! ## EML Specialization -/


variable {n : ℕ} (Φ : Fin n → C(X, ℝ))














omit [T2Space X] in
theorem solution    {A : Set C(X, ℝ)} {m : ℕ}
    (hA : ∀ f : C(X, ℝ), f ∈ closure A) :
    ∀ F : C(X, Fin m → ℝ), F ∈ closure (VecClass A m) := by
  -- Fix an arbitrary $F \in C(X, Fin m → ℝ)$ and an arbitrary $\epsilon > 0$.
  have h_eps : ∀ F : C(X, Fin m → ℝ), ∀ ε > 0, ∃ G : C(X, Fin m → ℝ), G ∈ VecClass A m ∧ ‖F - G‖ < ε := by
    intro F ε hε
    have h_coord : ∀ i : Fin m, ∃ g : C(X, ℝ), g ∈ A ∧ ‖(coordMap m i).comp F - g‖ < ε := by
      intro i;
      simpa [ dist_eq_norm ] using Metric.mem_closure_iff.mp ( hA _ ) ε hε;
    choose g hg hg' using h_coord
    use assembleVec g
    constructor
    · exact assembleVec_mem_vecClass hg
    ·
      rw [ ContinuousMap.norm_lt_iff _ hε ] at *;
      simp_all +decide [ ContinuousMap.norm_lt_iff, Pi.norm_def ];
      intro x; induction' ( Finset.univ : Finset ( Fin m ) ) using Finset.induction <;> aesop;
  intro F;
  rw [ Metric.mem_closure_iff ];
  simpa only [ dist_eq_norm ] using h_eps F
