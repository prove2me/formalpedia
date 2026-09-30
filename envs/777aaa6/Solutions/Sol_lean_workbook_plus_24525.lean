-- Prove2me | solution 1 for lean_workbook_plus_24525
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:47:48.833719+00:00
-- url     : https://prove2.me/submissions/8b1afc2c-8835-43bc-a1ae-27436c913c69

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace UnitCubeSumProductRange

def value (a b c : ℝ) : ℝ := a + b + c - a * b * c

def closedValues : Set ℝ := {v | ∃ a b c : ℝ,
  a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 ∧ value a b c = v}

def openValues : Set ℝ := {v | ∃ a b c : ℝ,
  a ∈ Set.Ioo 0 1 ∧ b ∈ Set.Ioo 0 1 ∧ c ∈ Set.Ioo 0 1 ∧ value a b c = v}

theorem upper_gap (a b c : ℝ) :
    2 - value a b c = (1 - a) * (1 - b) + (1 - c) * (1 - a * b) := by
  dsimp [value]
  ring

theorem coordinate_lower_bounds (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    a ≤ value a b c ∧ b ≤ value a b c ∧ c ≤ value a b c := by
  have hab : a * b ≤ 1 := mul_le_one₀ ha.2 hb.1 hb.2
  have hac : a * c ≤ 1 := mul_le_one₀ ha.2 hc.1 hc.2
  have hbc : b * c ≤ 1 := mul_le_one₀ hb.2 hc.1 hc.2
  have h1 := mul_nonneg ha.1 (sub_nonneg.mpr hbc)
  have h2 := mul_nonneg hb.1 (sub_nonneg.mpr hac)
  have h3 := mul_nonneg hc.1 (sub_nonneg.mpr hab)
  dsimp [value]
  constructor
  · nlinarith only [h3, hb.1]
  constructor
  · nlinarith only [h3, ha.1]
  · nlinarith only [h2, ha.1]

theorem closed_bounds (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    value a b c ∈ Set.Icc 0 2 := by
  have hab : a * b ≤ 1 := mul_le_one₀ ha.2 hb.1 hb.2
  have h := upper_gap a b c
  have h1 := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
  have h2 := mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hab)
  exact ⟨ha.1.trans (coordinate_lower_bounds a b c ha hb hc).1, by linarith only [h, h1, h2]⟩

theorem open_bounds (a b c : ℝ)
    (ha : a ∈ Set.Ioo 0 1) (hb : b ∈ Set.Ioo 0 1) (hc : c ∈ Set.Ioo 0 1) :
    value a b c ∈ Set.Ioo 0 2 := by
  have ha' : a ∈ Set.Icc 0 1 := ⟨ha.1.le, ha.2.le⟩
  have hb' : b ∈ Set.Icc 0 1 := ⟨hb.1.le, hb.2.le⟩
  have hc' : c ∈ Set.Icc 0 1 := ⟨hc.1.le, hc.2.le⟩
  have hab : a * b ≤ 1 := mul_le_one₀ ha.2.le hb.1.le hb.2.le
  have h := upper_gap a b c
  have h1 := mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)
  have h2 := mul_nonneg (sub_nonneg.mpr hc.2.le) (sub_nonneg.mpr hab)
  exact ⟨ha.1.trans_le (coordinate_lower_bounds a b c ha' hb' hc').1,
    by linarith only [h, h1, h2]⟩

theorem zero_equality (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    value a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro he
    have h := coordinate_lower_bounds a b c ha hb hc
    rw [he] at h
    exact ⟨le_antisymm h.1 ha.1, le_antisymm h.2.1 hb.1, le_antisymm h.2.2 hc.1⟩
  · rintro ⟨rfl, rfl, rfl⟩
    dsimp [value]
    ring

theorem two_equality (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    value a b c = 2 ↔ (a = 1 ∧ b = 1) ∨ (b = 1 ∧ c = 1) ∨ (c = 1 ∧ a = 1) := by
  constructor
  · intro he
    have hab : a * b ≤ 1 := mul_le_one₀ ha.2 hb.1 hb.2
    have h := upper_gap a b c
    have h1 := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
    have h2 := mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hab)
    have hzero : (1 - a) * (1 - b) = 0 := by linarith only [h, h1, h2, he]
    rcases mul_eq_zero.mp hzero with ha1 | hb1
    · have ha1 : a = 1 := by linarith only [ha1]
      subst a
      have hbc : (1 - b) * (1 - c) = 0 := by dsimp [value] at he; nlinarith only [he]
      rcases mul_eq_zero.mp hbc with hb1 | hc1
      · exact Or.inl ⟨rfl, by linarith only [hb1]⟩
      · exact Or.inr (Or.inr ⟨by linarith only [hc1], rfl⟩)
    · have hb1 : b = 1 := by linarith only [hb1]
      subst b
      have hac : (1 - a) * (1 - c) = 0 := by dsimp [value] at he; nlinarith only [he]
      rcases mul_eq_zero.mp hac with ha1 | hc1
      · exact Or.inl ⟨by linarith only [ha1], rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, by linarith only [hc1]⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> dsimp [value] <;> ring

theorem diagonal_strictMono : StrictMonoOn (fun t : ℝ => value t t t) (Set.Icc 0 1) := by
  intro s hs t ht hst
  have hs1 : s < 1 := hst.trans_le ht.2
  have hs2 : s ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hs1) (by linarith [hs.1] : 0 < 1 + s)]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by linarith [ht.1] : 0 ≤ 1 + t)]
  have hst1 : s * t ≤ 1 := mul_le_one₀ hs.2 ht.1 ht.2
  have hp := mul_pos (sub_pos.mpr hst) (show 0 < 3 - (t ^ 2 + s * t + s ^ 2) by linarith)
  dsimp [value]
  nlinarith only [hp]

theorem diagonal_preimage (v : ℝ) (hv : v ∈ Set.Icc 0 2) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ value t t t = v := by
  have hf : Continuous (fun t : ℝ => value t t t) := by unfold value; fun_prop
  have hzero : value 0 0 0 = 0 := by dsimp [value]; ring
  have hone : value 1 1 1 = 2 := by dsimp [value]; ring
  have hv' : v ∈ Set.Icc (value 0 0 0) (value 1 1 1) := by rwa [hzero, hone]
  exact intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn hv'

theorem unique_open_diagonal_preimage (v : ℝ) (hv : v ∈ Set.Ioo 0 2) :
    ∃! t : ℝ, t ∈ Set.Ioo 0 1 ∧ value t t t = v := by
  obtain ⟨t, ht, he⟩ := diagonal_preimage v ⟨hv.1.le, hv.2.le⟩
  have ht0 : 0 < t := by
    by_contra h
    have hz : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    subst t
    dsimp [value] at he
    nlinarith only [he, hv.1]
  have ht1 : t < 1 := by
    by_contra h
    have hz : t = 1 := le_antisymm ht.2 (le_of_not_gt h)
    subst t
    dsimp [value] at he
    nlinarith only [he, hv.2]
  refine ⟨t, ⟨⟨ht0, ht1⟩, he⟩, ?_⟩
  rintro s ⟨hs, hse⟩
  exact diagonal_strictMono.injOn ⟨hs.1.le, hs.2.le⟩ ht (hse.trans he.symm)

theorem closed_range : closedValues = Set.Icc 0 2 := by
  ext v
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    exact closed_bounds a b c ha hb hc
  · intro hv
    obtain ⟨t, ht, he⟩ := diagonal_preimage v hv
    exact ⟨t, t, t, ht, ht, ht, he⟩

theorem open_range : openValues = Set.Ioo 0 2 := by
  ext v
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    exact open_bounds a b c ha hb hc
  · intro hv
    obtain ⟨t, ⟨ht, he⟩, _⟩ := unique_open_diagonal_preimage v hv
    exact ⟨t, t, t, ht, ht, ht, he⟩

theorem closed_minimum : IsLeast closedValues 0 := by
  rw [closed_range]
  exact ⟨⟨le_rfl, by norm_num⟩, fun _ h => h.1⟩

theorem closed_maximum : IsGreatest closedValues 2 := by
  rw [closed_range]
  exact ⟨⟨by norm_num, le_rfl⟩, fun _ h => h.2⟩

theorem no_open_minimum (v : ℝ) : ¬ IsLeast openValues v := by
  rw [open_range]
  rintro ⟨hv, hmin⟩
  have hm : v / 2 ∈ Set.Ioo (0 : ℝ) 2 := by constructor <;> linarith [hv.1, hv.2]
  have h := hmin hm
  linarith [hv.1]

theorem no_open_maximum (v : ℝ) : ¬ IsGreatest openValues v := by
  rw [open_range]
  rintro ⟨hv, hmax⟩
  have hm : (v + 2) / 2 ∈ Set.Ioo (0 : ℝ) 2 := by constructor <;> linarith [hv.1, hv.2]
  have h := hmax hm
  linarith [hv.2]

end UnitCubeSumProductRange

theorem solution (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hc : 0 < c ∧ c < 1) : a + b + c - a * b * c < 2 :=
  (UnitCubeSumProductRange.open_bounds a b c ha hb hc).2

#print axioms UnitCubeSumProductRange.upper_gap
#print axioms UnitCubeSumProductRange.coordinate_lower_bounds
#print axioms UnitCubeSumProductRange.closed_bounds
#print axioms UnitCubeSumProductRange.open_bounds
#print axioms UnitCubeSumProductRange.zero_equality
#print axioms UnitCubeSumProductRange.two_equality
#print axioms UnitCubeSumProductRange.diagonal_strictMono
#print axioms UnitCubeSumProductRange.diagonal_preimage
#print axioms UnitCubeSumProductRange.unique_open_diagonal_preimage
#print axioms UnitCubeSumProductRange.closed_range
#print axioms UnitCubeSumProductRange.open_range
#print axioms UnitCubeSumProductRange.closed_minimum
#print axioms UnitCubeSumProductRange.closed_maximum
#print axioms UnitCubeSumProductRange.no_open_minimum
#print axioms UnitCubeSumProductRange.no_open_maximum
#print axioms solution
