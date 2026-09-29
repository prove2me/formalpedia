-- Prove2me | solution 1 for approx_simplex_interior
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:01:27.996044+00:00
-- url     : https://prove2.me/submissions/959de8df-01a0-4cbd-a1a2-7a7c014269c8

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

omit [T2Space X] in
/-- Density of the coupled class follows from density of the coordinatewise class. -/
theorem dense_coupledVecClass_of_dense_scalar
    {A : Set C(X, ℝ)} {m : ℕ}
    (hA : ∀ f : C(X, ℝ), f ∈ closure A) :
    ∀ F : C(X, Fin m → ℝ), F ∈ closure (CoupledVecClass A m) := by
  intro F
  exact closure_mono vecClass_subset_coupledVecClass (closure_vecClass_eq_univ_of_scalar hA F)

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
theorem solution    {A : Set C(X, ℝ)} {m : ℕ} (hm : 0 < m)
    (hA : ∀ f : C(X, ℝ), f ∈ closure A)
    {F : C(X, Fin m → ℝ)}
    (hF : ∀ x, F x ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ x i, 0 < F x i) :
    F ∈ closure {G | ∃ H ∈ CoupledVecClass A m, G = (softmaxMap m hm).comp H} := by
  -- Let z be the logit coordinates of F.
  set z : C(X, Fin m → ℝ) := ⟨fun x i => Real.log (F x i), by
    exact continuous_pi_iff.mpr fun i => Continuous.log ( F.continuous.comp continuous_id' |> Continuous.comp ( continuous_apply i ) ) fun x => ne_of_gt ( hpos x i )⟩
  generalize_proofs at *;
  -- Since softmaxMap is continuous, for H close enough to z, softmax(H) is close to softmax(z) = F.
  have h_cont : Continuous (fun H : C(X, Fin m → ℝ) => (softmaxMap m hm).comp H) := by
    refine' ContinuousMap.continuous_of_continuous_uncurry _ _;
    apply Continuous.comp (softmaxMap m hm).continuous;
    fun_prop
  generalize_proofs at *;
  -- Since $z$ is in the closure of $CoupledVecClass A m$, there exists a sequence $\{H_n\}$ in $CoupledVecClass A m$ such that $H_n \to z$.
  obtain ⟨H_seq, hH_seq⟩ : ∃ H_seq : ℕ → C(X, Fin m → ℝ), (∀ n, H_seq n ∈ CoupledVecClass A m) ∧ Filter.Tendsto H_seq Filter.atTop (nhds z) := by
    have h_dense : z ∈ closure (CoupledVecClass A m) := by
      convert dense_coupledVecClass_of_dense_scalar hA z;
    rw [ mem_closure_iff_seq_limit ] at h_dense ; tauto;
  have hF_eq_softmax_z : F = (softmaxMap m hm).comp z := by
    ext x i; simp +decide [ softmaxMap ] ;
    simp +decide [ z, Real.exp_log ( hpos x _ ), hF x |>.2 ];
  exact hF_eq_softmax_z ▸ mem_closure_of_tendsto ( h_cont.continuousAt.tendsto.comp hH_seq.2 ) ( Filter.Eventually.of_forall fun n => ⟨ H_seq n, hH_seq.1 n, rfl ⟩ )
