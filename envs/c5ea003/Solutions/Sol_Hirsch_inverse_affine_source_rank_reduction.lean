-- Prove2me | solution 1 for Hirsch.inverse_affine_source_rank_reduction
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-23T13:23:11.137663+00:00
-- url     : https://prove2.me/submissions/209c0f1c-9b5a-4bda-9989-39f60393a627

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.InverseRank

variable {d : ℕ}
abbrev Slope (d : ℕ) := (Fin d → ℝ) →ₗ[ℝ] ℝ

def height (h D : Slope d) (v z : Fin d → ℝ) : ℝ :=
  (1+D (z-v))/h (z-v)

def ratio (h D : Slope d) (v z : Fin d → ℝ) : ℝ :=
  h (z-v)/(1+D (z-v))

noncomputable def upper (S : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) : Finset ℝ := by
  classical
  exact ((S.erase v).image (height h D v)).filter (fun a => height h D v x<a)

noncomputable def lower (S : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) : Finset ℝ := by
  classical
  exact (S.image (ratio h D v)).filter (fun a => a<ratio h D v x)

/-- A shift parallel to the numerator translates every non-target inverse height. -/
lemma height_shift (h D : Slope d) (v z : Fin d → ℝ) (c : ℝ)
    (hz : h (z-v) ≠ 0) :
    height h (D+c • h) v z=height h D v z+c := by
  change (1+(D (z-v)+c*h (z-v)))/h (z-v)=(1+D (z-v))/h (z-v)+c
  field_simp [hz]
  <;> ring

/-- The inverse-height upper spectrum translates exactly; its size never changes. -/
theorem upper_shift (S : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) (c : ℝ) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ S, z ≠ v → 0<h (z-v)) :
    upper S h (D+c • h) v x=(upper S h D v x).image (fun a => a+c) := by
  classical
  have hs := height_shift h D v x c (ne_of_gt (hh x hx hxv))
  ext a
  constructor
  · intro ha
    obtain ⟨hai,hal⟩ := Finset.mem_filter.mp ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hai
    have hzS := (Finset.mem_erase.mp hz).2
    have hzv := (Finset.mem_erase.mp hz).1
    have he := height_shift h D v z c (ne_of_gt (hh z hzS hzv))
    refine Finset.mem_image.mpr ⟨height h D v z,?_,he.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,?_⟩
    rw [hs,he] at hal
    linarith
  · intro ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hai,hal⟩ := Finset.mem_filter.mp hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hai
    have hzS := (Finset.mem_erase.mp hz).2
    have hzv := (Finset.mem_erase.mp hz).1
    have he := height_shift h D v z c (ne_of_gt (hh z hzS hzv))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨z,hz,he⟩,?_⟩
    rw [hs]
    linarith

lemma upper_shift_card (S : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) (c : ℝ) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ S, z ≠ v → 0<h (z-v)) :
    (upper S h (D+c • h) v x).card=(upper S h D v x).card := by
  classical
  rw [upper_shift S h D v x c hx hxv hh]
  exact Finset.card_image_of_injective _ (fun a b hab => add_right_cancel hab)

/-- A common height shift enforces positivity on a larger finite set, without
changing any inverse-height comparison. No feasibility oracle is required. -/
theorem global_positive_shift (C : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) (hx : x ∈ C) (hxv : x ≠ v)
    (hh : ∀ z ∈ C, z ≠ v → 0<h (z-v)) :
    ∃ c : ℝ, ∀ z ∈ C, 0<1+(D+c • h) (z-v) := by
  classical
  have hxE : x ∈ C.erase v := Finset.mem_erase.mpr ⟨hxv,hx⟩
  obtain ⟨w,hw,hmin⟩ := Finset.exists_min_image (C.erase v) (height h D v) ⟨x,hxE⟩
  let c : ℝ := 1-height h D v w
  refine ⟨c,?_⟩
  intro z hz
  by_cases hzv : z=v
  · simp [hzv]
  · have hp := hh z hz hzv
    have hlo := hmin z (Finset.mem_erase.mpr ⟨hzv,hz⟩)
    have hval : height h (D+c • h) v z=height h D v z+c :=
      height_shift h D v z c (ne_of_gt hp)
    have hpos : 0<height h (D+c • h) v z := by
      rw [hval]
      dsimp [c]
      linarith
    change 0<(1+(D+c • h) (z-v))/h (z-v) at hpos
    have hprod := mul_pos hpos hp
    rw [div_mul_cancel₀ _ (ne_of_gt hp)] at hprod
    exact hprod

lemma ratio_inverse (h D : Slope d) (v z : Fin d → ℝ) :
    ratio h D v z=1/height h D v z := by
  simp only [ratio,height,one_div,inv_div]

lemma reverse_order (h D : Slope d) (v x z : Fin d → ℝ)
    (hx : 0<h (x-v)) (hz : 0<h (z-v))
    (qx : 0<1+D (x-v)) (qz : 0<1+D (z-v)) :
    ratio h D v z<ratio h D v x ↔ height h D v x<height h D v z := by
  have px : 0<height h D v x := div_pos qx hx
  have pz : 0<height h D v z := div_pos qz hz
  rw [ratio_inverse,ratio_inverse]
  rw [div_lt_div_iff₀ pz px]
  simp only [one_mul]

/-- The target contributes one value (zero); every other lower ratio corresponds
bijectively to an inverse height strictly ABOVE the source. -/
theorem lower_card (S : Finset (Fin d → ℝ)) (h D : Slope d)
    (v x : Fin d → ℝ) (hv : v ∈ S) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ S, z ≠ v → 0<h (z-v))
    (hq : ∀ z ∈ S, 0<1+D (z-v)) :
    (lower S h D v x).card=(upper S h D v x).card+1 := by
  classical
  have hxpos := hh x hx hxv
  have rxpos : 0<ratio h D v x := div_pos hxpos (hq x hx)
  have rvzero : ratio h D v v=0 := by simp [ratio]
  have he : lower S h D v x=insert 0 ((upper S h D v x).image (fun a => 1/a)) := by
    ext a
    constructor
    · intro ha
      obtain ⟨hai,hal⟩ := Finset.mem_filter.mp ha
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hai
      by_cases hzv : z=v
      · subst z
        exact Finset.mem_insert.mpr (Or.inl rvzero)
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨height h D v z,?_,(ratio_inverse h D v z).symm⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_image.mpr ⟨z,Finset.mem_erase.mpr ⟨hzv,hz⟩,rfl⟩,?_⟩
        exact (reverse_order h D v x z hxpos (hh z hz hzv) (hq x hx) (hq z hz)).mp hal
    · intro ha
      rcases Finset.mem_insert.mp ha with ha | ha
      · subst a
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v,hv,rvzero⟩,rxpos⟩
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hai,hal⟩ := Finset.mem_filter.mp hb
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hai
        have hzS := (Finset.mem_erase.mp hz).2
        have hzv := (Finset.mem_erase.mp hz).1
        rw [← ratio_inverse]
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z,hzS,rfl⟩,
          (reverse_order h D v x z hxpos (hh z hzS hzv) (hq x hx) (hq z hzS)).mpr hal⟩
  have hn : (0 : ℝ) ∉ (upper S h D v x).image (fun a => 1/a) := by
    intro hz
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hz
    obtain ⟨hai,hal⟩ := Finset.mem_filter.mp ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hai
    have hzS := (Finset.mem_erase.mp hz).2
    have hzv := (Finset.mem_erase.mp hz).1
    have hp : 0<height h D v z := div_pos (hq z hzS) (hh z hzS hzv)
    exact (ne_of_gt (div_pos (by norm_num : (0:ℝ)<1) hp)) heq
  have hinj : Function.Injective (fun a : ℝ => 1/a) := by
    intro a b heq
    have hi := congrArg (fun t : ℝ => t⁻¹) heq
    simpa only [one_div,inv_inv] using hi
  rw [he,Finset.card_insert_of_notMem hn,Finset.card_image_of_injective _ hinj]

/-- The positivity-constrained source rank has an exact unconstrained affine-
height formulation. A minimizing denominator can be positive on ALL of C,
even when its rank is optimized only on the smaller set S. -/
theorem optimum (C S : Finset (Fin d → ℝ)) (h : Slope d)
    (v x : Fin d → ℝ) (hSC : S ⊆ C) (hv : v ∈ S) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ C, z ≠ v → 0<h (z-v)) :
    ∃ D : Slope d, (∀ z ∈ C, 0<1+D (z-v)) ∧
      (lower S h D v x).card=(upper S h D v x).card+1 ∧
      (∀ E : Slope d, (upper S h D v x).card ≤ (upper S h E v x).card) ∧
      (∀ E : Slope d, (∀ z ∈ S, 0<1+E (z-v)) →
        (lower S h D v x).card ≤ (lower S h E v x).card) := by
  classical
  have hhS : ∀ z ∈ S, z ≠ v → 0<h (z-v) := fun z hz => hh z (hSC hz)
  have hex : ∃ n : ℕ, ∃ D : Slope d, (upper S h D v x).card=n := ⟨_,0,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  have hmin : ∀ E : Slope d, (upper S h D v x).card ≤ (upper S h E v x).card := by
    intro E
    rw [hD]
    exact Nat.find_min' hex ⟨E,rfl⟩
  obtain ⟨c,hc⟩ := global_positive_shift C h D v x (hSC hx) hxv hh
  let E := D+c • h
  have he : (upper S h E v x).card=(upper S h D v x).card :=
    upper_shift_card S h D v x c hx hxv hhS
  have hl : (lower S h E v x).card=(upper S h E v x).card+1 :=
    lower_card S h E v x hv hx hxv hhS (fun z hz => hc z (hSC hz))
  refine ⟨E,hc,hl,?_,?_⟩
  · intro F
    rw [he]
    exact hmin F
  · intro F hF
    rw [hl,lower_card S h F v x hv hx hxv hhS hF,he]
    exact Nat.add_le_add_right (hmin F) 1

/-- The slope directions controlling pair comparisons lie in ker(h): the
numerator-parallel degree of freedom is irrelevant to all level comparisons. -/
lemma normalized_direction (h : Slope d) (v z w : Fin d → ℝ)
    (hz : h (z-v) ≠ 0) (hw : h (w-v) ≠ 0) :
    h ((h (z-v))⁻¹ • (z-v)-(h (w-v))⁻¹ • (w-v))=0 := by
  rw [map_sub,map_smul,map_smul]
  simp only [smul_eq_mul,inv_mul_cancel₀ hz,inv_mul_cancel₀ hw,sub_self]

end Hirsch.InverseRank

/-- An unconstrained affine-height optimum exactly recovers the positive
normalized source rank, with a globally positive attaining denominator. -/
theorem solution (d : ℕ) (C S : Finset (Fin d → ℝ))
    (h : (Fin d → ℝ) →ₗ[ℝ] ℝ) (v x : Fin d → ℝ)
    (hSC : S ⊆ C) (hv : v ∈ S) (hx : x ∈ S) (hxv : x ≠ v)
    (hh : ∀ z ∈ C, z ≠ v → 0<h (z-v)) :
    let U := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
      @Finset.filter ℝ (fun a => (1+D (x-v))/h (x-v)<a)
        (fun _ => Classical.propDecidable _)
        ((S.erase v).image (fun z => (1+D (z-v))/h (z-v)))
    let R := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
      @Finset.filter ℝ (fun a => a<h (x-v)/(1+D (x-v)))
        (fun _ => Classical.propDecidable _)
        (S.image (fun z => h (z-v)/(1+D (z-v))))
    (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ, ∃ c : ℝ,
      (∀ z ∈ C, 0<1+(D+c • h) (z-v)) ∧ (U (D+c • h)).card=(U D).card) ∧
    (∀ D : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ S, 0<1+D (z-v)) →
      (R D).card=(U D).card+1) ∧
    (∀ z ∈ C, z ≠ v → ∀ w ∈ C, w ≠ v →
      h ((h (z-v))⁻¹ • (z-v)-(h (w-v))⁻¹ • (w-v))=0) ∧
    ∃ D : (Fin d → ℝ) →ₗ[ℝ] ℝ,
      (∀ z ∈ C, 0<1+D (z-v)) ∧ (R D).card=(U D).card+1 ∧
      (∀ E : (Fin d → ℝ) →ₗ[ℝ] ℝ, (U D).card ≤ (U E).card) ∧
      (∀ E : (Fin d → ℝ) →ₗ[ℝ] ℝ, (∀ z ∈ S, 0<1+E (z-v)) →
        (R D).card ≤ (R E).card) := by
  classical
  let U := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
    @Finset.filter ℝ (fun a => (1+D (x-v))/h (x-v)<a)
      (fun _ => Classical.propDecidable _)
      ((S.erase v).image (fun z => (1+D (z-v))/h (z-v)))
  let R := fun D : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
    @Finset.filter ℝ (fun a => a<h (x-v)/(1+D (x-v)))
      (fun _ => Classical.propDecidable _)
      (S.image (fun z => h (z-v)/(1+D (z-v))))
  have hU : ∀ D, Hirsch.InverseRank.upper S h D v x=U D := by
    intro D
    ext a
    simp only [Hirsch.InverseRank.upper,Hirsch.InverseRank.height,U,
      Finset.mem_filter,Finset.mem_image]
  have hR : ∀ D, Hirsch.InverseRank.lower S h D v x=R D := by
    intro D
    ext a
    simp only [Hirsch.InverseRank.lower,Hirsch.InverseRank.ratio,R,
      Finset.mem_filter,Finset.mem_image]
  have hhS : ∀ z ∈ S, z ≠ v → 0<h (z-v) := fun z hz => hh z (hSC hz)
  refine ⟨?_,?_,?_,?_⟩
  · intro D
    obtain ⟨c,hc⟩ := Hirsch.InverseRank.global_positive_shift C h D v x (hSC hx) hxv hh
    refine ⟨c,hc,?_⟩
    simpa only [hU] using Hirsch.InverseRank.upper_shift_card S h D v x c hx hxv hhS
  · intro D hD
    simpa only [hU,hR] using Hirsch.InverseRank.lower_card S h D v x hv hx hxv hhS hD
  · intro z hz hzv w hw hwv
    exact Hirsch.InverseRank.normalized_direction h v z w
      (ne_of_gt (hh z hz hzv)) (ne_of_gt (hh w hw hwv))
  · obtain ⟨D,hD,he,hu,hr⟩ := Hirsch.InverseRank.optimum C S h v x hSC hv hx hxv hh
    refine ⟨D,hD,?_,?_,?_⟩
    · simpa only [hU,hR] using he
    · simpa only [hU] using hu
    · simpa only [hR] using hr

#print axioms Hirsch.InverseRank.upper_shift
#print axioms Hirsch.InverseRank.global_positive_shift
#print axioms Hirsch.InverseRank.lower_card
#print axioms Hirsch.InverseRank.optimum
#print axioms Hirsch.InverseRank.normalized_direction
#print axioms solution
