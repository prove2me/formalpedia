-- Prove2me | solution 1 for Hirsch.normalized_tangent_slice_lifts_to_image_edge
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T21:46:28.072733+00:00
-- url     : https://prove2.me/submissions/cdeaac97-9b6c-4b7b-aba8-2ec80f32efef

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.NormalizedImageTangent
variable {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]

/-- Finite strict slack constructs a feasible positive step for EVERY active
inequality direction. Source vertexhood and bounded source fibres are absent. -/
lemma feasible_tangent_step
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (J : Finset ι) (x v : E)
    (hx : ∀ i, a i x ≤ b i) (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i)
    (hv : ∀ i ∈ J, a i v ≤ 0) :
    ∃ s : ℝ, 0 < s ∧ ∀ i, a i (x+s • v) ≤ b i := by
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
  let s := r o/2
  have hs : 0 < s := div_pos (hr o ho) (by norm_num)
  refine ⟨s, hs, ?_⟩
  intro i
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases hi : i ∈ J
  · have hmul := mul_nonpos_of_nonneg_of_nonpos hs.le (hv i hi)
    linarith [hJ i hi]
  · have hm := hmin (some i) (by simp [T])
    have hm' : r o ≤ (b i-a i x)/(|a i v|+1) := by
      simpa only [r, if_neg hi] using hm
    have hsmall : s < (b i-a i x)/(|a i v|+1) := by
      dsimp [s]
      linarith [hr o ho]
    have hp := (lt_div_iff₀ (by positivity : 0 < |a i v|+1)).mp hsmall
    have hu := mul_le_mul_of_nonneg_left (le_abs_self (a i v)) hs.le
    nlinarith

/-- The projected active-row cone is exactly the nonnegative cone of actual
image displacements. No closure or hidden source-edge premise is needed. -/
lemma exact_image_tangent
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x : E)
    (hx : ∀ i, a i x ≤ b i) (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i) :
    G '' {v : E | ∀ i ∈ J, a i v ≤ 0} =
      {w : F | ∃ s : ℝ, 0 ≤ s ∧ ∃ z : E,
        (∀ i, a i z ≤ b i) ∧ w = s • (G z-G x)} := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, hs, hstep⟩ := feasible_tangent_step a b J x v hx hJ hstrict hv
    refine ⟨s⁻¹, (inv_pos.mpr hs).le, x+s • v, hstep, ?_⟩
    simp only [map_add, map_smul, add_sub_cancel_left, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hs), one_smul]
  · rintro ⟨s, hs, z, hz, rfl⟩
    refine ⟨s • (z-x), ?_, ?_⟩
    · intro i hi
      have hn : a i (z-x) ≤ 0 := by
        rw [map_sub, hJ i hi]
        exact sub_nonpos.mpr (hz i)
      simpa only [map_smul, smul_eq_mul] using mul_nonpos_of_nonneg_of_nonpos hs hn
    · simp only [map_smul, map_sub]

/-- Strictly positive selected-row weights and a finite image factorization
make height positive on every nonzero IMAGE direction, even with source lines. -/
lemma height_positive_modulo_image_kernel
    (a : ι → E →ₗ[ℝ] ℝ) (G : E →ₗ[ℝ] F) (J : Finset ι)
    (h : F →ₗ[ℝ] ℝ) (lam : ι → ℝ) (W : ι → F)
    (hlam : ∀ i ∈ J, 0 < lam i)
    (hheight : h.comp G = -(∑ i ∈ J, lam i • a i))
    (himage : ∀ v : E, G v = ∑ i ∈ J, a i v • W i)
    (v : E) (hv : ∀ i ∈ J, a i v ≤ 0) :
    0 ≤ h (G v) ∧ (h (G v) = 0 → G v = 0) := by
  have he := congrArg (fun L : E →ₗ[ℝ] ℝ => L v) hheight
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul] at he
  have hs : h (G v) = ∑ i ∈ J, lam i * (-a i v) := by
    simpa only [mul_neg, Finset.sum_neg_distrib] using he
  have hnon : ∀ i ∈ J, 0 ≤ lam i * (-a i v) := fun i hi =>
    mul_nonneg (hlam i hi).le (neg_nonneg.mpr (hv i hi))
  refine ⟨by rw [hs]; exact Finset.sum_nonneg hnon, ?_⟩
  intro hz
  have hai : ∀ i ∈ J, a i v = 0 := by
    intro i hi
    have hle : lam i * (-a i v) ≤ ∑ j ∈ J, lam j * (-a j v) :=
      Finset.single_le_sum hnon hi
    rw [← hs, hz] at hle
    have hm : lam i * (-a i v) = 0 := le_antisymm hle (hnon i hi)
    have ht := (mul_eq_zero.mp hm).resolve_left (ne_of_gt (hlam i hi))
    linarith
  rw [himage]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hai i hi, zero_smul]

/-- A singleton support in the normalized IMAGE slice produces a supporting
ray of the full image cone. A merely optimal nonunique direction is not enough. -/
lemma normalized_slice_support_ray
    (a : ι → E →ₗ[ℝ] ℝ) (G : E →ₗ[ℝ] F) (J : Finset ι)
    (h f : F →ₗ[ℝ] ℝ) (r : F) (hr : h r = 1)
    (hpos : ∀ v : E, (∀ i ∈ J, a i v ≤ 0) →
      0 ≤ h (G v) ∧ (h (G v) = 0 → G v = 0))
    (hslice : ∀ v : E, (∀ i ∈ J, a i v ≤ 0) → h (G v) = 1 →
      f (G v) ≤ f r ∧ (f (G v) = f r → G v = r)) :
    ∀ v : E, (∀ i ∈ J, a i v ≤ 0) →
      (f-(f r) • h) (G v) ≤ 0 ∧
      ((f-(f r) • h) (G v) = 0 ↔ G v = h (G v) • r) := by
  intro v hv
  have hnon := (hpos v hv).1
  by_cases hz : h (G v) = 0
  · have hg := (hpos v hv).2 hz
    simp [hg]
  · have ht : 0 < h (G v) := lt_of_le_of_ne hnon (Ne.symm hz)
    let t := h (G v)
    have ht0 : t ≠ 0 := hz
    have hv' : ∀ i ∈ J, a i (t⁻¹ • v) ≤ 0 := by
      intro i hi
      simpa only [map_smul, smul_eq_mul] using
        mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hnon) (hv i hi)
    have hn : h (G (t⁻¹ • v)) = 1 := by
      simp only [map_smul, smul_eq_mul]
      exact inv_mul_cancel₀ ht0
    obtain ⟨hbound, hsingle⟩ := hslice (t⁻¹ • v) hv' hn
    have hbound' : t⁻¹ * f (G v) ≤ f r := by
      simpa only [map_smul, smul_eq_mul] using hbound
    have hmul := mul_le_mul_of_nonneg_left hbound' hnon
    change t * (t⁻¹ * f (G v)) ≤ t * f r at hmul
    have hscaled : f (G v) ≤ t * f r := by
      simpa only [← mul_assoc, mul_inv_cancel₀ ht0, one_mul] using hmul
    have heval : (f-(f r) • h) (G v) = f (G v)-f r*t := rfl
    refine ⟨by rw [heval]; nlinarith, ?_⟩
    constructor
    · intro he
      have hf : f (G v) = t * f r := by rw [heval] at he; nlinarith
      have hnormeq : f (G (t⁻¹ • v)) = f r := by
        simp only [map_smul, smul_eq_mul, hf, ← mul_assoc, inv_mul_cancel₀ ht0, one_mul]
      have hray := hsingle hnormeq
      have hm := congrArg (fun z : F => t • z) hray
      simpa only [map_smul, smul_smul, mul_inv_cancel₀ ht0, one_smul] using hm
    · intro he
      rw [he]
      simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr]
      ring

-- Supporting slices are extreme; same elementary argument as accepted #246.
lemma support_extreme (P : Set F) (f : F →ₗ[ℝ] ℝ) (beta : ℝ)
    (hb : ∀ z ∈ P, f z ≤ beta) :
    IsExtreme ℝ P {z | z ∈ P ∧ f z = beta} := by
  refine ⟨fun z hz => hz.1, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  obtain ⟨r,s,hr,hs,hrs,he⟩ := hseg
  have he' := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at he'
  have heq : r*f x+s*f y = beta := he'.trans hz.2
  by_contra hne
  have hlt : f x < beta := lt_of_le_of_ne (hb x hx) hne
  have h1 := mul_lt_mul_of_pos_left hlt hr
  have h2 := mul_le_mul_of_nonneg_left (hb y hy) hs.le
  have hsum : r*beta+s*beta = beta := by rw [← add_mul, hrs, one_mul]
  linarith

#print axioms feasible_tangent_step
#print axioms exact_image_tangent
#print axioms height_positive_modulo_image_kernel
#print axioms normalized_slice_support_ray
end Hirsch.NormalizedImageTangent

/-- Construct an original IMAGE supporting edge from normalized tangent-slice
support and an optimal ray length over all lifts. No source adjacency, source
vertex, source compactness, original edge or original edge exposer is assumed.
The normalized slice support is supplied by the accepted fibre-dual interface;
its LP production is distinct from this exact geometric implication. -/
theorem solution
    {E F ι : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [Fintype ι] [DecidableEq ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (G : E →ₗ[ℝ] F)
    (J : Finset ι) (x y : E) (r : F) (tau : ℝ)
    (h f c : F →ₗ[ℝ] ℝ) (lam : ι → ℝ) (W : ι → F)
    (hx : ∀ i, a i x ≤ b i) (hy : ∀ i, a i y ≤ b i)
    (hJ : ∀ i ∈ J, a i x = b i)
    (hstrict : ∀ i, i ∉ J → a i x < b i)
    (hlam : ∀ i ∈ J, 0 < lam i)
    (hheight : h.comp G = -(∑ i ∈ J, lam i • a i))
    (himage : ∀ v : E, G v = ∑ i ∈ J, a i v • W i)
    (hr : h r = 1) (htau : 0 < tau) (hcr : 0 < c r)
    (hslice : ∀ v : E, (∀ i ∈ J, a i v ≤ 0) → h (G v) = 1 →
      f (G v) ≤ f r ∧ (f (G v) = f r → G v = r))
    (hyimage : G y = G x+tau • r)
    (hcap : ∀ z : E, (∀ i, a i z ≤ b i) → ∀ t : ℝ,
      G z = G x+t • r → t ≤ tau) :
    let P := {z : E | ∀ i, a i z ≤ b i}
    let ell := f-(f r) • h
    (G '' {v : E | ∀ i ∈ J, a i v ≤ 0} =
      {w : F | ∃ s : ℝ, 0 ≤ s ∧ ∃ z ∈ P, w = s • (G z-G x)}) ∧
    (∀ z ∈ G '' P, ell z ≤ ell (G x)) ∧
    {z | z ∈ G '' P ∧ ell z = ell (G x)} = segment ℝ (G x) (G y) ∧
    G x ≠ G y ∧ IsExtreme ℝ (G '' P) (segment ℝ (G x) (G y)) ∧
    c (G x) < c (G y) := by
  classical
  dsimp only
  let ell := f-(f r) • h
  have hpos := Hirsch.NormalizedImageTangent.height_positive_modulo_image_kernel
    a G J h lam W hlam hheight himage
  have hcone := Hirsch.NormalizedImageTangent.normalized_slice_support_ray a G J h f r hr hpos hslice
  have hdiff : ∀ z : E, (∀ i, a i z ≤ b i) → ∀ i ∈ J, a i (z-x) ≤ 0 := by
    intro z hz i hi
    rw [map_sub, hJ i hi]
    exact sub_nonpos.mpr (hz i)
  have hbound : ∀ z ∈ G '' {z : E | ∀ i, a i z ≤ b i}, ell z ≤ ell (G x) := by
    rintro w ⟨z, hz, rfl⟩
    have hh := (hcone (z-x) (hdiff z hz)).1
    change ell (G (z-x)) ≤ 0 at hh
    rw [map_sub, map_sub] at hh
    linarith
  have hellr : ell r = 0 := by
    simp only [ell, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hr, mul_one, sub_self]
  have helly : ell (G y) = ell (G x) := by
    rw [hyimage, map_add, map_smul, hellr, smul_zero, add_zero]
  have heq : {z | z ∈ G '' {z : E | ∀ i, a i z ≤ b i} ∧ ell z = ell (G x)} =
      segment ℝ (G x) (G y) := by
    ext w
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, he⟩
      have hzcone := hdiff z hz
      have h0 : ell (G (z-x)) = 0 := by rw [map_sub, map_sub, he, sub_self]
      have hline := (hcone (z-x) hzcone).2.mp h0
      have hn := (hpos (z-x) hzcone).1
      let t := h (G (z-x))
      have hzimage : G z = G x+t • r := by
        calc
          G z = G x+(G z-G x) := by abel
          _ = G x+t • r := by rw [← map_sub, hline]
      have ht := hcap z hz t hzimage
      have hquot : 0 ≤ t/tau := div_nonneg hn htau.le
      have hquot1 : t/tau ≤ 1 := (div_le_iff₀ htau).mpr (by simpa only [one_mul] using ht)
      refine ⟨1-t/tau, t/tau, by linarith, hquot, by ring, ?_⟩
      calc
        (1-t/tau) • G x+(t/tau) • G y = G x+((t/tau)*tau) • r := by rw [hyimage]; module
        _ = G x+t • r := by rw [div_mul_cancel₀ _ (ne_of_gt htau)]
        _ = G z := hzimage.symm
    · rintro ⟨s,t,hs,ht,hst,he⟩
      have hz : ∀ i, a i (s • x+t • y) ≤ b i := by
        intro i
        simp only [map_add, map_smul, smul_eq_mul]
        calc
          s*a i x+t*a i y ≤ s*b i+t*b i :=
            add_le_add (mul_le_mul_of_nonneg_left (hx i) hs) (mul_le_mul_of_nonneg_left (hy i) ht)
          _ = b i := by rw [← add_mul, hst, one_mul]
      refine ⟨⟨s • x+t • y, hz, ?_⟩, ?_⟩
      · simpa only [map_add, map_smul] using he
      · rw [← he, map_add, map_smul, map_smul, helly, ← add_smul, hst, one_smul]
  have hne : G x ≠ G y := by
    intro he
    have hh := congrArg h hyimage
    rw [← he] at hh
    simp only [map_add, map_smul, smul_eq_mul, hr, mul_one] at hh
    linarith
  have hext : IsExtreme ℝ (G '' {z : E | ∀ i, a i z ≤ b i}) (segment ℝ (G x) (G y)) := by
    rw [← heq]
    exact Hirsch.NormalizedImageTangent.support_extreme _ ell _ hbound
  have himprove : c (G x) < c (G y) := by
    rw [hyimage, map_add, map_smul]
    change c (G x) < c (G x)+tau*c r
    linarith [mul_pos htau hcr]
  exact ⟨Hirsch.NormalizedImageTangent.exact_image_tangent a b G J x hx hJ hstrict,
    hbound, heq, hne, hext, himprove⟩

#print axioms solution
