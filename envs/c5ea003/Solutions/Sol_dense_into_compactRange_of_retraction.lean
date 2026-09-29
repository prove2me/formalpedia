-- Prove2me | solution 1 for dense_into_compactRange_of_retraction
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:07:05.04988+00:00
-- url     : https://prove2.me/submissions/4a44fc01-7963-449e-a242-ebdb9561d806

-- Sol generated from Bridges/HilbertSpace/VectorStoneWeierstrass.lean
import Mathlib
import Definitions.Def_Bridges_HilbertSpace_VectorStoneWeierstrass
import Theorems.Thm_closure_vecClass_eq_univ_of_scalar
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
omit [T2Space X] in
theorem exists_mem_vecClass_uniformApprox
    {A : Set C(X, ℝ)} {m : ℕ}
    (hA : ∀ f : C(X, ℝ), f ∈ closure A)
    (F : C(X, Fin m → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ G ∈ VecClass A m, ‖F - G‖ < ε := by
  -- Apply the closure result to the vector function $F$ to find a sequence of functions in $VecClass A m$ converging to $F$.
  have h_closure : F ∈ closure (VecClass A m) :=
    closure_vecClass_eq_univ_of_scalar hA F
  -- Apply the Metric.mem_closure_iff theorem to get the existence of such a G.
  rw [Metric.mem_closure_iff] at h_closure;
  simpa only [ dist_eq_norm ] using h_closure ε hε


/-! ## Coupled Vector Class -/


/-
`VecClass A m ⊆ CoupledVecClass A m`: use identity readout with `k = m`.
-/
omit [CompactSpace X] [T2Space X] in
theorem vecClass_subset_coupledVecClass
    {A : Set C(X, ℝ)} {m : ℕ} :
    VecClass A m ⊆ CoupledVecClass A m := by
  intro F hF;
  use m;
  -- Let `g j` be the `j`-th coordinate projection of `F`, which is in `A` by definition of `VecClass`.
  use fun j => (coordMap m j).comp F;
  exact ⟨ hF, ⟨ ContinuousMap.id _, by ext; rfl ⟩ ⟩


/-
Closure under continuous output postcomposition.
-/
omit [CompactSpace X] [T2Space X] in
theorem comp_mem_coupledVecClass
    {A : Set C(X, ℝ)} {m p : ℕ}
    {F : C(X, Fin m → ℝ)} (hF : F ∈ CoupledVecClass A m)
    (ψ : C(Fin m → ℝ, Fin p → ℝ)) :
    ψ.comp F ∈ CoupledVecClass A p := by
  obtain ⟨ k, g, hg, φ, rfl ⟩ := hF;
  exact ⟨ k, g, hg, ψ.comp φ, rfl ⟩

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
    (hA : ∀ f : C(X, ℝ), f ∈ closure A)
    {r : C(Fin m → ℝ, Fin m → ℝ)}
    {K : Set (Fin m → ℝ)}
    (hrK : ∀ y ∈ K, r y = y)
    (hrange : ∀ y, r y ∈ K)
    {F : C(X, Fin m → ℝ)} (hFK : ∀ x, F x ∈ K) :
    ∀ ε > 0, ∃ G : C(X, Fin m → ℝ),
      G ∈ CoupledVecClass A m ∧ (∀ x, G x ∈ K) ∧ dist F G < ε := by
  intro ε hε
  -- By the continuity of `r`, we have `r.comp F = F`.
  have h_comp_eq : r.comp F = F := by
    aesop;
  -- By the continuity of `r`, we have `r.comp` is continuous.
  have h_comp_cont : Continuous (r.comp · : C(X, Fin m → ℝ) → C(X, Fin m → ℝ)) :=
    continuous_postcomp r
  -- Since `r.comp` is continuous, for any `ε > 0`, there exists a `δ > 0` such that if `dist G F < δ`, then `dist (r.comp G) (r.comp F) < ε`.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ G : C(X, Fin m → ℝ), dist G F < δ → dist (r.comp G) (r.comp F) < ε := by
    exact Metric.continuous_iff.mp h_comp_cont F ε hε;
  obtain ⟨ G, hG₁, hG₂ ⟩ := exists_mem_vecClass_uniformApprox hA F hδ_pos;
  refine' ⟨ r.comp G, _, _, _ ⟩;
  · exact comp_mem_coupledVecClass ( vecClass_subset_coupledVecClass hG₁ ) r;
  · exact fun x => hrange _;
  · simpa [ dist_eq_norm', h_comp_eq, norm_sub_rev ] using hδ G ( by simpa [ dist_eq_norm', norm_sub_rev ] using hG₂ )
