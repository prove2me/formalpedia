-- Prove2me | solution 1 for lean_workbook_plus_18879
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:13:58.142451+00:00
-- url     : https://prove2.me/submissions/aac8a9ff-6e78-45da-a262-8893202133d8

import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

theorem monotone_nonnegative_of_unique_positive_fibers (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0)
    (hnonneg : ∀ x, 0 ≤ x → 0 ≤ f x)
    (hinj : ∀ u v, 0 ≤ u → 0 ≤ v → f u = f v → 0 < f u → u = v) :
    MonotoneOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  by_contra hle
  have hyx : f y < f x := lt_of_not_ge hle
  let c : ℝ := (f x + f y) / 2
  have hc0 : 0 < c := by dsimp [c]; linarith [hnonneg y hy]
  have hcy : f y < c := by dsimp [c]; linarith
  have hcx : c < f x := by dsimp [c]; linarith
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hx
    (hf.mono (fun _ ht => ht.1)) (show c ∈ Set.Icc (f 0) (f x) from
      ⟨by rw [hf0]; exact hc0.le, hcx.le⟩)
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hxy
    (hf.mono (fun _ ht => le_trans hx ht.1))
    (show c ∈ Set.Icc (f y) (f x) from ⟨hcy.le, hcx.le⟩)
  have huv : u = v := hinj u v hu.1 (le_trans hx hv.1)
    (hfu.trans hfv.symm) (by rw [hfu]; exact hc0)
  have hux : u = x := by linarith [hu.2, hv.1]
  rw [hux] at hfu
  linarith

theorem continuous_sqrt_iteration_classification (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0)) (hnonneg : ∀ x, 0 ≤ x → 0 ≤ f x) :
    (∀ x, 0 ≤ x → f (f x) = Real.sqrt (x * f x)) ↔
      (∀ x, 0 ≤ x → f x = 0) ∨ (∀ x, 0 ≤ x → f x = x) := by
  constructor
  · intro hfe
    have hff0 : f (f 0) = 0 := by
      simpa only [zero_mul, Real.sqrt_zero] using hfe 0 le_rfl
    have hf0 : f 0 = 0 := by
      have h := hfe (f 0) (hnonneg 0 le_rfl)
      rw [hff0, mul_zero, Real.sqrt_zero] at h
      exact h
    have hsq (x : ℝ) (hx : 0 ≤ x) : f (f x) ^ 2 = x * f x := by
      rw [hfe x hx]
      exact Real.sq_sqrt (mul_nonneg hx (hnonneg x hx))
    have hinj (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
        (huv : f u = f v) (hpos : 0 < f u) : u = v := by
      have h1 := hsq u hu
      have h2 := hsq v hv
      rw [huv] at h1 hpos
      exact mul_right_cancel₀ (ne_of_gt hpos) (h1.symm.trans h2)
    have hm := monotone_nonnegative_of_unique_positive_fibers f hf hf0 hnonneg hinj
    have hpoint (x : ℝ) (hx : 0 ≤ x) : f x = 0 ∨ f x = x := by
      by_cases hzero : f x = 0
      · exact Or.inl hzero
      right
      have hfx : 0 ≤ f x := hnonneg x hx
      have hpos : 0 < f x := lt_of_le_of_ne hfx (Ne.symm hzero)
      have hff : 0 ≤ f (f x) := hnonneg (f x) hfx
      have hs := hsq x hx
      rcases lt_trichotomy (f x) x with hlt | heq | hgt
      · have hbound : f (f x) ≤ f x := hm hfx hx hlt.le
        have hprod := mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hfx hff)
        nlinarith [mul_pos hpos (sub_pos.mpr hlt)]
      · exact heq
      · have hbound : f x ≤ f (f x) := hm hx hfx hgt.le
        have hprod := mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hff hfx)
        nlinarith [mul_pos hpos (sub_pos.mpr hgt)]
    by_cases hzero : ∀ x, 0 ≤ x → f x = 0
    · exact Or.inl hzero
    right
    push_neg at hzero
    obtain ⟨a, ha, hfa⟩ := hzero
    have hfa_pos : 0 < f a := lt_of_le_of_ne (hnonneg a ha) (Ne.symm hfa)
    intro x hx
    rcases hpoint x hx with hxzero | hxid
    · by_cases hx0 : x = 0
      · subst x
        exact hf0
      have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      let c : ℝ := min x (f a) / 2
      have hcpos : 0 < c := half_pos (lt_min hxpos hfa_pos)
      have hcx : c < x := by dsimp [c]; linarith [min_le_left x (f a)]
      have hca : c ≤ f a := by dsimp [c]; linarith [min_le_right x (f a)]
      obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ha
        (hf.mono (fun _ ht => ht.1)) (show c ∈ Set.Icc (f 0) (f a) from
          ⟨by rw [hf0]; exact hcpos.le, hca⟩)
      rcases hpoint u hu.1 with hu0 | huid
      · rw [hu0] at hfu
        linarith
      · have hux : u ≤ x := by linarith
        have hbound := hm hu.1 hx hux
        rw [hfu, hxzero] at hbound
        linarith
    · exact hxid
  · rintro (hzero | hid) x hx
    · simp only [hzero x hx, hzero 0 le_rfl, mul_zero, Real.sqrt_zero]
    · simp only [hid x hx]
      exact (Real.sqrt_mul_self hx).symm

theorem solution (f : ℝ → ℝ) (hf : Continuous f)
    (h : f '' Set.Ici 0 ⊆ Set.Ici 0)
    (hf2 : ∀ x ∈ Set.Ici 0, f (f x) = Real.sqrt (x * f x)) :
    ∃ g : ℝ → ℝ, Continuous g ∧ g '' Set.Ici 0 ⊆ Set.Ici 0 ∧
      (∀ x ∈ Set.Ici 0, g (g x) = Real.sqrt (x * g x)) := by
  have hnonneg : ∀ x, 0 ≤ x → 0 ≤ f x := fun x hx => h ⟨x, hx, rfl⟩
  have hc := (continuous_sqrt_iteration_classification f hf.continuousOn hnonneg).mp hf2
  refine ⟨f, hf, h, ?_⟩
  exact (continuous_sqrt_iteration_classification f hf.continuousOn hnonneg).mpr hc

#print axioms monotone_nonnegative_of_unique_positive_fibers
#print axioms continuous_sqrt_iteration_classification
#print axioms solution
