-- Prove2me | solution 1 for Hirsch.parallel_support_bridge_uniform_endpoint_exposers
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T15:19:00.848671+00:00
-- url     : https://prove2.me/submissions/217a1321-8d13-4d62-894c-328c889c7383

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Hirsch.BridgeEndpointExposers
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A single positive radius preserves every originally strict comparison,
for both perturbation signs and EVERY smaller positive parameter. -/
lemma uniform_two_sided_radius (D : Finset E) (f q : E →ₗ[ℝ] ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∀ x ∈ D, 0 < f x → 0 < (f-s • q) x ∧ 0 < (f+s • q) x := by
  classical
  let radius : Option E → ℝ := fun x => match x with
    | none => 1
    | some x => if 0 < f x then f x / (|q x|+1) else 1
  let T : Finset (Option E) := insert none (D.image some)
  have hr : ∀ x ∈ T, 0 < radius x := by
    intro x _
    cases x with
    | none => norm_num [radius]
    | some x =>
      dsimp [radius]
      split_ifs with hx
      · exact div_pos hx (by positivity)
      · norm_num
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image T radius ⟨none, by simp [T]⟩
  refine ⟨radius x₀/2, div_pos (hr x₀ hx₀) (by norm_num), ?_⟩
  intro s hs hsδ x hx hfx
  have hm := hmin (some x) (by simp [T, hx])
  have hm' : radius x₀ ≤ f x/(|q x|+1) := by
    simpa only [radius, if_pos hfx] using hm
  have hsmall : s < f x/(|q x|+1) := by linarith [hr x₀ hx₀]
  have hp := (lt_div_iff₀ (by positivity : 0 < |q x|+1)).mp hsmall
  have hl := neg_abs_le (q x)
  have hu := le_abs_self (q x)
  have h₁ := mul_le_mul_of_nonneg_left hl hs.le
  have h₂ := mul_le_mul_of_nonneg_left hu hs.le
  change 0 < f x-s*q x ∧ 0 < f x+s*q x
  constructor <;> nlinarith

/-- On a segment parallel to e, the normalized coordinate identifies its
endpoints, even when the segment collapses to a point. -/
lemma segment_coordinate (e a b x : E) (η : ℝ) (q : E →ₗ[ℝ] ℝ)
    (hq : q e = 1) (hη : 0 ≤ η) (hb : b = a+η • e)
    (hx : x ∈ segment ℝ a b) :
    (q a ≤ q x ∧ q x ≤ q b) ∧
      (q x = q a → x = a) ∧ (q x = q b → x = b) := by
  obtain ⟨r, s, hr, hs, hrs, hcomb⟩ := hx
  have hpoint : x = a+(s*η) • e := by
    rw [← hcomb, hb, smul_add, smul_smul, ← add_assoc, ← add_smul, hrs, one_smul]
  have hval : q x = q a+s*η := by
    rw [hpoint]
    simp only [map_add, map_smul, smul_eq_mul, hq, mul_one]
  have hbval : q b = q a+η := by
    rw [hb]
    simp only [map_add, map_smul, smul_eq_mul, hq, mul_one]
  have hprod : 0 ≤ s*η := mul_nonneg hs hη
  have hs1 : s ≤ 1 := by linarith
  have hprod1 : s*η ≤ η := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs1 hη
  refine ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩
  · intro he
    have hz : s*η = 0 := by linarith
    simpa only [hz, zero_smul, add_zero] using hpoint
  · intro he
    have hz : s*η = η := by linarith
    rw [hz] at hpoint
    exact hpoint.trans hb.symm

private lemma active_scalar {a c x y β : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hac : a+c = 1)
    (hx : x ≤ β) (hy : y ≤ β) (he : a*x+c*y = β) : x = β := by
  by_contra hn
  have hlt : x < β := lt_of_le_of_ne hx hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hy hc
  have hscale : a*β+c*β = β := by rw [← add_mul, hac, one_mul]
  linarith

/-- The finite strict comparison certificate exposes the WHOLE convex hull
at a singleton, not merely a unique listed maximizer. -/
lemma hull_unique_support (S : Finset E) (p : E) (f : E →ₗ[ℝ] ℝ)
    (hstrict : ∀ x ∈ S, x ≠ p → f x < f p) :
    ∀ x ∈ convexHull ℝ (S : Set E), f x ≤ f p ∧ (f x = f p → x = p) := by
  let good : Set E := {x | f x ≤ f p ∧ (f x = f p → x = p)}
  have hgood : Convex ℝ good := by
    intro x hx y hy r s hr hs hrs
    have he : f (r • x+s • y) = r*f x+s*f y := by simp
    have h₁ := mul_le_mul_of_nonneg_left hx.1 hr
    have h₂ := mul_le_mul_of_nonneg_left hy.1 hs
    refine ⟨?_, ?_⟩
    · rw [he]
      calc
        r*f x+s*f y ≤ r*f p+s*f p := add_le_add h₁ h₂
        _ = f p := by rw [← add_mul, hrs, one_mul]
    · intro ht
      by_cases hr0 : r = 0
      · have hs1 : s = 1 := by linarith
        simpa [hr0, hs1] using hy.2 (by simpa [hr0, hs1] using ht)
      by_cases hs0 : s = 0
      · have hr1 : r = 1 := by linarith
        simpa [hs0, hr1] using hx.2 (by simpa [hs0, hr1] using ht)
      have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have htop : r*f x+s*f y = f p := he.symm.trans ht
      have hxeq := hx.2 (active_scalar hrpos hs hrs hx.1 hy.1 htop)
      have hyeq := hy.2 (active_scalar hspos hr (by linarith) hy.1 hx.1 (by nlinarith))
      rw [hxeq, hyeq, ← add_smul, hrs, one_smul]
  apply convexHull_min _ hgood
  intro x hx
  by_cases he : x = p
  · subst x
    exact ⟨le_rfl, fun _ => rfl⟩
  · exact ⟨(hstrict x hx he).le, fun h => False.elim ((ne_of_lt (hstrict x hx he)) h)⟩

/-- Strict component support gives a unique whole-sum exposed endpoint;
this includes the empty sum and lower-dimensional point factors. -/
lemma sum_unique_support (m : ℕ) (S : Fin m → Finset E) (p : Fin m → E)
    (hp : ∀ i, p i ∈ S i) (f : E →ₗ[ℝ] ℝ)
    (hs : ∀ i x, x ∈ S i → x ≠ p i → f x < f (p i)) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    (∑ i, p i) ∈ R ∧ ∀ z ∈ R,
      f z ≤ f (∑ i, p i) ∧ (f z = f (∑ i, p i) → z = ∑ i, p i) := by
  classical
  dsimp only
  refine ⟨⟨p, fun i => subset_convexHull ℝ (S i : Set E) (hp i), rfl⟩, ?_⟩
  intro z hz
  obtain ⟨x, hx, hsum⟩ := hz
  have hh : ∀ i, f (x i) ≤ f (p i) ∧ (f (x i) = f (p i) → x i = p i) :=
    fun i => hull_unique_support (S i) (p i) f (hs i) (x i) (hx i)
  constructor
  · rw [← hsum, map_sum, map_sum]
    exact Finset.sum_le_sum (fun i _ => (hh i).1)
  · intro he
    have hx' : x = p := by
      funext i
      apply (hh i).2
      by_contra hn
      have hlt : f (x i) < f (p i) := lt_of_le_of_ne (hh i).1 hn
      have hc : (∑ j, f (x j)) < ∑ j, f (p j) := by
        apply Finset.sum_lt_sum
        · intro j _
          exact (hh j).1
        · exact ⟨i, Finset.mem_univ _, hlt⟩
      rw [← hsum, map_sum, map_sum] at he
      exact (ne_of_lt hc) he
    rw [hx'] at hsum
    exact hsum.symm

/-- Endpoint compatibility for an already constructed parallel-support bridge.
The functionals and a common open perturbation radius are constructed, not
provided by a vertex-exposure oracle. -/
theorem uniform_endpoint_exposers
    (m : ℕ) (S : Fin m → Finset E)
    (a b : Fin m → E) (η : Fin m → ℝ) (e : E)
    (he : e ≠ 0) (f : E →ₗ[ℝ] ℝ) (hf : f e = 0)
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ S i)
    (hη : ∀ i, 0 ≤ η i) (hba : ∀ i, b i = a i+η i • e)
    (hbound : ∀ i x, x ∈ S i → f x ≤ f (a i))
    (hface : ∀ i x, x ∈ S i → f x = f (a i) → x ∈ segment ℝ (a i) (b i)) :
    ∃ (q : E →ₗ[ℝ] ℝ) (δ : ℝ), q e = 1 ∧ 0 < δ ∧
      ∀ s : ℝ, 0 < s → s < δ →
        (∀ i x, x ∈ S i → x ≠ a i → (f-s • q) x < (f-s • q) (a i)) ∧
        (∀ i x, x ∈ S i → x ≠ b i → (f+s • q) x < (f+s • q) (b i)) := by
  classical
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ)
    (fun _ : Unit => e) (fun _ => he)
  let q : E →ₗ[ℝ] ℝ := (g e)⁻¹ • g
  have hq : q e = 1 := by
    change (g e)⁻¹*g e = 1
    exact inv_mul_cancel₀ (hg ())
  let D : Finset E := Finset.univ.biUnion fun i : Fin m =>
    ((S i).image fun x => a i-x) ∪ ((S i).image fun x => b i-x)
  have hd₁ : ∀ i x, x ∈ S i → a i-x ∈ D := by
    intro i x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  have hd₂ : ∀ i x, x ∈ S i → b i-x ∈ D := by
    intro i x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
  obtain ⟨δ, hδ, hsmall⟩ := uniform_two_sided_radius D f q
  refine ⟨q, δ, hq, hδ, ?_⟩
  intro s hs hsδ
  have hbval : ∀ i, f (b i) = f (a i) := by
    intro i
    rw [hba i]
    simp only [map_add, map_smul, smul_eq_mul, hf, mul_zero, add_zero]
  constructor
  · intro i x hx hxa
    by_cases ht : f x = f (a i)
    · have hc := segment_coordinate e (a i) (b i) x (η i) q hq (hη i) (hba i) (hface i x hx ht)
      have hlt : q (a i) < q x := lt_of_le_of_ne hc.1.1 (fun hh => hxa (hc.2.1 hh.symm))
      have hm := mul_pos hs (sub_pos.mpr hlt)
      change f x-s*q x < f (a i)-s*q (a i)
      rw [ht]
      nlinarith
    · have hpos : 0 < f (a i-x) := by
        rw [map_sub]
        exact sub_pos.mpr (lt_of_le_of_ne (hbound i x hx) ht)
      have hh := (hsmall s hs hsδ (a i-x) (hd₁ i x hx) hpos).1
      exact sub_pos.mp (by simpa only [map_sub] using hh)
  · intro i x hx hxb
    by_cases ht : f x = f (a i)
    · have hc := segment_coordinate e (a i) (b i) x (η i) q hq (hη i) (hba i) (hface i x hx ht)
      have hlt : q x < q (b i) := lt_of_le_of_ne hc.1.2 (fun hh => hxb (hc.2.2 hh))
      have hm := mul_pos hs (sub_pos.mpr hlt)
      change f x+s*q x < f (b i)+s*q (b i)
      rw [ht, hbval i]
      nlinarith
    · have hpos : 0 < f (b i-x) := by
        rw [map_sub, hbval i]
        exact sub_pos.mpr (lt_of_le_of_ne (hbound i x hx) ht)
      have hh := (hsmall s hs hsδ (b i-x) (hd₂ i x hx) hpos).2
      exact sub_pos.mp (by simpa only [map_sub] using hh)

#print axioms uniform_two_sided_radius
#print axioms segment_coordinate
#print axioms hull_unique_support
#print axioms sum_unique_support
#print axioms uniform_endpoint_exposers
end Hirsch.BridgeEndpointExposers

/-- Uniform strict endpoint objectives for the SAME components and whole sum
as a parallel exposed bridge. Point factors and empty families are allowed. -/
theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m : ℕ) (S : Fin m → Finset E)
    (a b : Fin m → E) (η : Fin m → ℝ) (e : E)
    (he : e ≠ 0) (f : E →ₗ[ℝ] ℝ) (hf : f e = 0)
    (ha : ∀ i, a i ∈ S i) (hb : ∀ i, b i ∈ S i)
    (hη : ∀ i, 0 ≤ η i) (hba : ∀ i, b i = a i+η i • e)
    (hbound : ∀ i x, x ∈ S i → f x ≤ f (a i))
    (hface : ∀ i x, x ∈ S i → f x = f (a i) → x ∈ segment ℝ (a i) (b i)) :
    let R : Set E := {z | ∃ x : Fin m → E,
      (∀ i, x i ∈ convexHull ℝ (S i : Set E)) ∧ (∑ i, x i) = z}
    ∃ (q : E →ₗ[ℝ] ℝ) (δ : ℝ), q e = 1 ∧ 0 < δ ∧
      (∑ i, a i) ∈ R ∧ (∑ i, b i) ∈ R ∧
      ∀ s : ℝ, 0 < s → s < δ →
        (∀ i x, x ∈ S i → x ≠ a i → (f-s • q) x < (f-s • q) (a i)) ∧
        (∀ i x, x ∈ S i → x ≠ b i → (f+s • q) x < (f+s • q) (b i)) ∧
        (∀ z ∈ R, (f-s • q) z ≤ (f-s • q) (∑ i, a i) ∧
          ((f-s • q) z = (f-s • q) (∑ i, a i) → z = ∑ i, a i)) ∧
        (∀ z ∈ R, (f+s • q) z ≤ (f+s • q) (∑ i, b i) ∧
          ((f+s • q) z = (f+s • q) (∑ i, b i) → z = ∑ i, b i)) := by
  classical
  dsimp only
  obtain ⟨q, δ, hq, hδ, hexpose⟩ :=
    Hirsch.BridgeEndpointExposers.uniform_endpoint_exposers m S a b η e he f hf ha hb hη hba hbound hface
  refine ⟨q, δ, hq, hδ,
    ⟨a, fun i => subset_convexHull ℝ (S i : Set E) (ha i), rfl⟩,
    ⟨b, fun i => subset_convexHull ℝ (S i : Set E) (hb i), rfl⟩, ?_⟩
  intro s hs hsδ
  obtain ⟨hl, hr⟩ := hexpose s hs hsδ
  exact ⟨hl, hr,
    (Hirsch.BridgeEndpointExposers.sum_unique_support m S a ha (f-s • q) hl).2,
    (Hirsch.BridgeEndpointExposers.sum_unique_support m S b hb (f+s • q) hr).2⟩

#print axioms solution
