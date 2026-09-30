-- Prove2me | solution 1 for Hirsch.projected_minimal_face_from_fibre_duals
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T21:06:40.425365+00:00
-- url     : https://prove2.me/submissions/4f1c0864-fd8d-47d1-96b6-2c823601c987

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.ProjectedFaceDiscovery
variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]

/-- A dual optimum on a fixed image fibre cannot use a row that is strict at
an anchor in that fibre. All coefficients still refer to ORIGINAL rows. -/
lemma dual_zero_off_active
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E) (lam : ι → ι → ℝ) (psi : ι → F →ₗ[ℝ] ℝ)
    (hx : ∀ j, a j x ≤ b j) (hJ : ∀ j ∈ J, a j x = b j)
    (hstrict : ∀ j, j ∉ J → a j x < b j)
    (hlam : ∀ i ∈ J, ∀ j, 0 ≤ lam i j)
    (hnormal : ∀ i ∈ J, -a i = (∑ j, lam i j • a j) + (psi i).comp G)
    (hvalue : ∀ i ∈ J, -b i = (∑ j, lam i j*b j) + psi i (G x)) :
    ∀ i ∈ J, ∀ j, j ∉ J → lam i j = 0 := by
  intro i hi j hj
  have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) (hnormal i hi)
  simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at he
  have hv := hvalue i hi
  have hix := hJ i hi
  have hs : (∑ k, lam i k*(b k-a k x)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have hnon : ∀ k, 0 ≤ lam i k*(b k-a k x) := fun k =>
    mul_nonneg (hlam i hi k) (sub_nonneg.mpr (hx k))
  have hle : lam i j*(b j-a j x) ≤ ∑ k, lam i k*(b k-a k x) :=
    Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)
  have hz : lam i j*(b j-a j x) = 0 := by linarith [hnon j]
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (sub_pos.mpr (hstrict j hj)))

/-- Construct the image exposer by SUMMING the row-optimality duals. Neither
an exposing image objective nor selected-row positive weights are supplied. -/
theorem constructed_exposer
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E) (lam : ι → ι → ℝ) (psi : ι → F →ₗ[ℝ] ℝ)
    (hx : ∀ j, a j x ≤ b j) (hJ : ∀ j ∈ J, a j x = b j)
    (hstrict : ∀ j, j ∉ J → a j x < b j)
    (hlam : ∀ i ∈ J, ∀ j, 0 ≤ lam i j)
    (hnormal : ∀ i ∈ J, -a i = (∑ j, lam i j • a j) + (psi i).comp G)
    (hvalue : ∀ i ∈ J, -b i = (∑ j, lam i j*b j) + psi i (G x)) :
    ∃ f : F →ₗ[ℝ] ℝ, ∀ z : E, (∀ j, a j z ≤ b j) →
      f (G z) ≤ f (G x) ∧
      (f (G z) = f (G x) ↔ ∀ j ∈ J, a j z = b j) := by
  have hzero := dual_zero_off_active a b G J x lam psi hx hJ hstrict hlam hnormal hvalue
  let f : F →ₗ[ℝ] ℝ := ∑ i ∈ J, -psi i
  have hcomponent : ∀ z : E, (∀ j, a j z ≤ b j) → ∀ i ∈ J,
      -psi i (G z) ≤ -psi i (G x) ∧
      b i-a i z ≤ -psi i (G x)-(-psi i (G z)) := by
    intro z hz i hi
    have he := congrArg (fun L : E →ₗ[ℝ] ℝ => L z) (hnormal i hi)
    simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at he
    have hv := hvalue i hi
    have hs : (∑ j, lam i j*a j z) ≤ ∑ j, lam i j*b j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hz j) (hlam i hi j))
    have hz' := hz i
    constructor <;> linarith
  refine ⟨f, ?_⟩
  intro z hz
  have hweak : f (G z) ≤ f (G x) := by
    simp only [f, LinearMap.sum_apply, LinearMap.neg_apply]
    exact Finset.sum_le_sum (fun i hi => (hcomponent z hz i hi).1)
  refine ⟨hweak, ?_⟩
  constructor
  · intro he i hi
    have he' : (∑ i ∈ J, -psi i (G z)) = ∑ i ∈ J, -psi i (G x) := by
      simpa only [f, LinearMap.sum_apply, LinearMap.neg_apply] using he
    have hsum : (∑ i ∈ J, (-psi i (G x)-(-psi i (G z)))) = 0 := by
      rw [Finset.sum_sub_distrib, he']
      exact sub_self _
    have hgap : ∀ j ∈ J, 0 ≤ -psi j (G x)-(-psi j (G z)) :=
      fun j hj => sub_nonneg.mpr (hcomponent z hz j hj).1
    have hi_le : -psi i (G x)-(-psi i (G z)) ≤
        ∑ j ∈ J, (-psi j (G x)-(-psi j (G z))) :=
      Finset.single_le_sum hgap hi
    have hrow := (hcomponent z hz i hi).2
    have hfeas := hz i
    linarith
  · intro he
    simp only [f, LinearMap.sum_apply, LinearMap.neg_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hs : (∑ j, lam i j*a j z) = ∑ j, lam i j*b j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ J
      · rw [he j hj]
      · rw [hzero i hi j hj]
        simp
    have hn := congrArg (fun L : E →ₗ[ℝ] ℝ => L z) (hnormal i hi)
    simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at hn
    have hv := hvalue i hi
    have hiz := he i hi
    linarith

/-- Every selected-kernel direction is realized by actual feasible perturbations
on BOTH sides of the strict anchor. No dimension or interior oracle is used. -/
theorem local_kernel_steps
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (J : Finset ι) (x v : E)
    (hx : ∀ i, a i x ≤ b i) (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i)
    (hv : ∀ i ∈ J, a i v = 0) :
    ∃ eps : ℝ, 0 < eps ∧
      (∀ i, a i (x+eps • v) ≤ b i) ∧ (∀ i, a i (x-eps • v) ≤ b i) ∧
      (∀ i ∈ J, a i (x+eps • v) = b i) ∧ (∀ i ∈ J, a i (x-eps • v) = b i) := by
  classical
  let r : Option ι → ℝ := fun o => match o with
    | none => 1
    | some i => if i ∈ J then 1 else (b i-a i x)/(|a i v|+1)
  let T : Finset (Option ι) := insert none (Finset.univ.image some)
  have hr : ∀ o ∈ T, 0 < r o := by
    intro o _
    cases o with
    | none => norm_num [r]
    | some i =>
      dsimp [r]
      split_ifs with hi
      · norm_num
      · exact div_pos (sub_pos.mpr (hstrict i hi)) (by positivity)
  obtain ⟨o, ho, hmin⟩ := Finset.exists_min_image T r ⟨none, by simp [T]⟩
  let eps := r o / 2
  have heps : 0 < eps := div_pos (hr o ho) (by norm_num)
  have hboth : ∀ i, a i (x+eps • v) ≤ b i ∧ a i (x-eps • v) ≤ b i := by
    intro i
    by_cases hi : i ∈ J
    · simp only [map_add, map_sub, map_smul, smul_eq_mul, hv i hi, mul_zero,
        add_zero, sub_zero]
      exact ⟨hx i, hx i⟩
    · have hm := hmin (some i) (by simp [T])
      have hm' : r o ≤ (b i-a i x)/(|a i v|+1) := by
        simpa only [r, if_neg hi] using hm
      have hsmall : eps < (b i-a i x)/(|a i v|+1) := by
        dsimp [eps]
        linarith [hr o ho]
      have hp := (lt_div_iff₀ (by positivity : 0 < |a i v|+1)).mp hsmall
      have hl := mul_le_mul_of_nonneg_left (neg_abs_le (a i v)) heps.le
      have hu := mul_le_mul_of_nonneg_left (le_abs_self (a i v)) heps.le
      simp only [map_add, map_sub, map_smul, smul_eq_mul]
      constructor <;> nlinarith
  refine ⟨eps, heps, fun i => (hboth i).1, fun i => (hboth i).2, ?_, ?_⟩
  · intro i hi
    simp only [map_add, map_smul, smul_eq_mul, hv i hi, mul_zero, add_zero, hJ i hi]
  · intro i hi
    simp only [map_sub, map_smul, smul_eq_mul, hv i hi, mul_zero, sub_zero, hJ i hi]

/-- The discovered face is the SMALLEST extreme subset containing the image
anchor, not merely some large supporting face containing it. -/
theorem minimal_image_face
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E)
    (hx : ∀ i, a i x ≤ b i) (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i)
    (D : Set F) (hD : IsExtreme ℝ (G '' {z | ∀ i, a i z ≤ b i}) D)
    (hDx : G x ∈ D) :
    G '' {z | (∀ i, a i z ≤ b i) ∧ ∀ i ∈ J, a i z = b i} ⊆ D := by
  rintro y ⟨z, ⟨hz, hzJ⟩, rfl⟩
  have hv : ∀ i ∈ J, a i (z-x) = 0 := by
    intro i hi
    simp only [map_sub, hzJ i hi, hJ i hi, sub_self]
  obtain ⟨eps, heps, _, hback, _, _⟩ := local_kernel_steps a b J x (z-x) hx hJ hstrict hv
  let s : ℝ := (1+eps)⁻¹
  let t : ℝ := eps*s
  have hs : 0 < s := inv_pos.mpr (by linarith)
  have ht : 0 < t := mul_pos heps hs
  have hts : t+s = 1 := by
    change eps*(1+eps)⁻¹+(1+eps)⁻¹=1
    calc
      eps*(1+eps)⁻¹+(1+eps)⁻¹ = (1+eps)*(1+eps)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ (by linarith)
  have hleft : t-s*eps = 0 := by dsimp [t]; ring
  have hright : s+s*eps = 1 := by
    have he : s+s*eps = t+s := by dsimp [t]; ring
    exact he.trans hts
  have heq : t • G z+s • G (x-eps • (z-x)) = G x := by
    simp only [map_sub, map_smul]
    calc
      t • G z+s • (G x-eps • (G z-G x)) =
          (t-s*eps) • G z+(s+s*eps) • G x := by module
      _ = G x := by rw [hleft, hright]; simp
  exact hD.left_mem_of_mem_openSegment ⟨z, hz, rfl⟩
    ⟨x-eps • (z-x), hback, rfl⟩ hDx ⟨t, s, ht, hs, hts, heq⟩

/-- Image directions of the whole discovered face generate exactly the same
linear tests as images of the selected-row kernel. This justifies the rank test. -/
theorem image_kernel_tests
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E)
    (hx : ∀ i, a i x ≤ b i) (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i) (W : Submodule ℝ F) :
    (∀ z : E, (∀ i, a i z ≤ b i) → (∀ i ∈ J, a i z = b i) → G z-G x ∈ W) ↔
      (∀ v : E, (∀ i ∈ J, a i v = 0) → G v ∈ W) := by
  constructor
  · intro h v hv
    obtain ⟨eps, heps, hf, _, he, _⟩ := local_kernel_steps a b J x v hx hJ hstrict hv
    have hm := h (x+eps • v) hf he
    have hm' : eps • G v ∈ W := by
      simpa only [map_add, map_smul, add_sub_cancel_left] using hm
    have hinv := W.smul_mem eps⁻¹ hm'
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt heps), one_smul] using hinv
  · intro h z _ hz
    have hv : ∀ i ∈ J, a i (z-x) = 0 := by
      intro i hi
      simp only [map_sub, hz i hi, hJ i hi, sub_self]
    simpa only [map_sub] using h (z-x) hv

-- Same proof as accepted #246, with namespace and bound-variable renaming.
lemma support_extreme (P : Set F) (f : F →ₗ[ℝ] ℝ) (beta : ℝ)
    (hb : ∀ z ∈ P, f z ≤ beta) :
    IsExtreme ℝ P {z | z ∈ P ∧ f z = beta} := by
  refine ⟨fun z hz => hz.1, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  obtain ⟨r,s,hr,hs,hrs,he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  have heq : r * f x + s * f y = beta := he'.trans hz.2
  by_contra hne
  have hlt : f x < beta := lt_of_le_of_ne (hb x hx) hne
  have h1 := mul_lt_mul_of_pos_left hlt hr
  have h2 := mul_le_mul_of_nonneg_left (hb y hy) hs.le
  have hsum : r * beta + s * beta = beta := by rw [← add_mul, hrs, one_mul]
  linarith

#print axioms dual_zero_off_active
#print axioms constructed_exposer
#print axioms local_kernel_steps
#print axioms minimal_image_face
#print axioms image_kernel_tests
end Hirsch.ProjectedFaceDiscovery

/-- Original-row fibre certificates construct the exact minimal exposed image
face and its full direction tests. No image exposer, compactness, source vertex,
source adjacency, or one-dimensional preimage is assumed. -/
theorem solution
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E) (lam : ι → ι → ℝ) (psi : ι → F →ₗ[ℝ] ℝ)
    (hx : ∀ j, a j x ≤ b j) (hJ : ∀ j ∈ J, a j x = b j)
    (hstrict : ∀ j, j ∉ J → a j x < b j)
    (hlam : ∀ i ∈ J, ∀ j, 0 ≤ lam i j)
    (hnormal : ∀ i ∈ J, -a i = (∑ j, lam i j • a j) + (psi i).comp G)
    (hvalue : ∀ i ∈ J, -b i = (∑ j, lam i j*b j) + psi i (G x)) :
    let P := {z : E | ∀ i, a i z ≤ b i}
    let H := {z : E | (∀ i, a i z ≤ b i) ∧ ∀ i ∈ J, a i z = b i}
    ∃ f : F →ₗ[ℝ] ℝ,
      (∀ y ∈ G '' P, f y ≤ f (G x)) ∧
      {y | y ∈ G '' P ∧ f y = f (G x)} = G '' H ∧
      IsExtreme ℝ (G '' P) (G '' H) ∧
      (∀ D : Set F, IsExtreme ℝ (G '' P) D → G x ∈ D → G '' H ⊆ D) ∧
      (∀ W : Submodule ℝ F,
        (∀ z ∈ H, G z-G x ∈ W) ↔
        (∀ v : E, (∀ i ∈ J, a i v = 0) → G v ∈ W)) := by
  classical
  dsimp only
  obtain ⟨f, hf⟩ := Hirsch.ProjectedFaceDiscovery.constructed_exposer
    a b G J x lam psi hx hJ hstrict hlam hnormal hvalue
  have hbound : ∀ y ∈ G '' {z : E | ∀ i, a i z ≤ b i}, f y ≤ f (G x) := by
    rintro y ⟨z, hz, rfl⟩
    exact (hf z hz).1
  have heq : {y | y ∈ G '' {z : E | ∀ i, a i z ≤ b i} ∧ f y = f (G x)} =
      G '' {z : E | (∀ i, a i z ≤ b i) ∧ ∀ i ∈ J, a i z = b i} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hval⟩
      exact ⟨z, ⟨hz, (hf z hz).2.mp hval⟩, rfl⟩
    · rintro ⟨z, ⟨hz, he⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hf z hz).2.mpr he⟩
  refine ⟨f, hbound, heq, ?_, ?_, ?_⟩
  · rw [← heq]
    exact Hirsch.ProjectedFaceDiscovery.support_extreme _ f _ hbound
  · intro D hD hxD
    exact Hirsch.ProjectedFaceDiscovery.minimal_image_face a b G J x hx hJ hstrict D hD hxD
  · intro W
    have h := Hirsch.ProjectedFaceDiscovery.image_kernel_tests a b G J x hx hJ hstrict W
    simpa only [Set.mem_setOf_eq, and_imp] using h

#print axioms solution
