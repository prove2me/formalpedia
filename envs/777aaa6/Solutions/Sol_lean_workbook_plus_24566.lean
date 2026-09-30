-- Prove2me | solution 1 for lean_workbook_plus_24566
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:20:07.076838+00:00
-- url     : https://prove2.me/submissions/2e54b1ee-4d5b-4602-a489-b743fc27020f

import Mathlib

set_option autoImplicit false

namespace CubicProductSumCore

def schurGap (a b c : Real) : Real :=
  (a + b + c) ^ 3 - 4 * (a + b + c) * (a * b + b * c + c * a) + 9 * a * b * c

def amgmGap (a b c : Real) : Real := (a + b + c) ^ 3 - 27 * a * b * c

def core (a b c : Real) : Real :=
  (135 * a * b * c + 4 * (a + b + c) ^ 3) * (a ^ 3 + b ^ 3 + c ^ 3) -
    (a + b + c) ^ 6

-- The weighted-square argument is reused from the local proved
-- linear/Solutions/CubicConstraintSharpSum.lean, theorem schur_nonneg.
theorem schur_nonneg (a b c : Real) (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    0 <= schurGap a b c := by
  have hschur :
      0 <= a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
    by_cases hs : a + b + c = 0
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      have hc0 : c = 0 := by linarith
      simp [ha0, hb0, hc0]
    · have hs0 : 0 < a + b + c := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      have hf : 0 < a + (b + c) / 4 := by linarith
      have hp : 0 <= (a + (b + c) / 4) *
          (a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b)) := by
        calc
          0 <= b * c * (b - c) ^ 2 +
              (c * a * (c - a) ^ 2 + a * b * (a - b) ^ 2) / 4 +
              (2 * a ^ 2 - b ^ 2 - c ^ 2 - a * b + 2 * b * c - c * a) ^ 2 / 4 := by
            positivity
          _ = _ := by ring
      exact nonneg_of_mul_nonneg_right hp hf
  have hid : schurGap a b c =
      a * (a - b) * (a - c) + b * (b - c) * (b - a) + c * (c - a) * (c - b) := by
    unfold schurGap
    ring
  rwa [hid]

theorem amgm_gap_identity (a b c : Real) :
    amgmGap a b c = (a + b - 2 * c) ^ 3 +
      (9 * c / 2) * ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) := by
  unfold amgmGap
  ring

theorem amgm_gap_min (a b c : Real) (hc : 0 <= c) (hca : c <= a) (hcb : c <= b) :
    0 <= amgmGap a b c /\ (amgmGap a b c = 0 -> a = c /\ b = c) := by
  have hbase : 0 <= a + b - 2 * c := by linarith
  have hcube : 0 <= (a + b - 2 * c) ^ 3 := pow_nonneg hbase _
  have hrest : 0 <= (9 * c / 2) * ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) := by
    positivity
  have hid := amgm_gap_identity a b c
  refine And.intro (by linarith) ?_
  intro he
  have hz : (a + b - 2 * c) ^ 3 = 0 := by linarith
  have hz' : a + b - 2 * c = 0 := eq_zero_of_pow_eq_zero hz
  exact And.intro (by linarith) (by linarith)

theorem amgm_gap_nonneg_and_eq (a b c : Real)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    0 <= amgmGap a b c /\ (amgmGap a b c = 0 <-> a = b /\ b = c) := by
  have h : 0 <= amgmGap a b c /\ (amgmGap a b c = 0 -> a = b /\ b = c) := by
    rcases le_total c (min a b) with hmin | hmin
    · have hca := hmin.trans (min_le_left _ _)
      have hcb := hmin.trans (min_le_right _ _)
      obtain ⟨hn, he⟩ := amgm_gap_min a b c hc hca hcb
      exact And.intro hn (fun hz => And.intro ((he hz).1.trans (he hz).2.symm) (he hz).2)
    · by_cases hab : a <= b
      · rw [min_eq_left hab] at hmin
        have hid : amgmGap b c a = amgmGap a b c := by unfold amgmGap; ring
        obtain ⟨hn, he⟩ := amgm_gap_min b c a ha hab hmin
        rw [hid] at hn he
        exact And.intro hn (fun hz => And.intro (he hz).1.symm ((he hz).1.trans (he hz).2.symm))
      · have hba : b <= a := le_of_not_ge hab
        rw [min_eq_right hba] at hmin
        have hid : amgmGap a c b = amgmGap a b c := by unfold amgmGap; ring
        obtain ⟨hn, he⟩ := amgm_gap_min a c b hb hba hmin
        rw [hid] at hn he
        exact And.intro hn (fun hz => And.intro (he hz).1 (he hz).2.symm)
  refine And.intro h.1 (Iff.intro h.2 ?_)
  rintro ⟨rfl, rfl⟩
  unfold amgmGap
  ring

theorem core_certificate (a b c : Real) :
    4 * core a b c =
      3 * (4 * (a + b + c) ^ 3 + 135 * a * b * c) * schurGap a b c +
        75 * a * b * c * amgmGap a b c := by
  unfold core schurGap amgmGap
  ring

theorem core_nonneg (a b c : Real) (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    0 <= core a b c := by
  have hR := schur_nonneg a b c ha hb hc
  have hH := (amgm_gap_nonneg_and_eq a b c ha hb hc).1
  have h1 : 0 <= 3 * (4 * (a + b + c) ^ 3 + 135 * a * b * c) * schurGap a b c := by
    positivity
  have h2 : 0 <= 75 * a * b * c * amgmGap a b c := by positivity
  have hid := core_certificate a b c
  linarith

theorem core_eq_zero_iff (a b c : Real) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    core a b c = 0 <-> a = b /\ b = c := by
  constructor
  · intro he
    have hR := schur_nonneg a b c ha.le hb.le hc.le
    have hH := amgm_gap_nonneg_and_eq a b c ha.le hb.le hc.le
    have h1 : 0 <= 3 * (4 * (a + b + c) ^ 3 + 135 * a * b * c) * schurGap a b c := by
      positivity
    have h2 : 0 <= 75 * a * b * c * amgmGap a b c := mul_nonneg (by positivity) hH.1
    have hid := core_certificate a b c
    have hz : 75 * a * b * c * amgmGap a b c = 0 := by linarith
    have hcoef : 75 * a * b * c ≠ 0 := ne_of_gt (by positivity)
    exact hH.2.mp ((mul_eq_zero.mp hz).resolve_left hcoef)
  · rintro ⟨rfl, rfl⟩
    unfold core
    ring

theorem homogeneous_nonneg (a b c : Real) (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c) :
    (a + b + c) ^ 6 <=
      (135 * a * b * c + 4 * (a + b + c) ^ 3) * (a ^ 3 + b ^ 3 + c ^ 3) :=
  sub_nonneg.mp (core_nonneg a b c ha hb hc)

theorem homogeneous_eq_iff (a b c : Real) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (135 * a * b * c + 4 * (a + b + c) ^ 3) * (a ^ 3 + b ^ 3 + c ^ 3) =
      (a + b + c) ^ 6 <-> a = b /\ b = c := by
  exact (sub_eq_zero.symm).trans (core_eq_zero_iff a b c ha hb hc)

end CubicProductSumCore

#print axioms CubicProductSumCore.schurGap
#print axioms CubicProductSumCore.amgmGap
#print axioms CubicProductSumCore.core
#print axioms CubicProductSumCore.schur_nonneg
#print axioms CubicProductSumCore.amgm_gap_identity
#print axioms CubicProductSumCore.amgm_gap_min
#print axioms CubicProductSumCore.amgm_gap_nonneg_and_eq
#print axioms CubicProductSumCore.core_certificate
#print axioms CubicProductSumCore.core_nonneg
#print axioms CubicProductSumCore.core_eq_zero_iff
#print axioms CubicProductSumCore.homogeneous_nonneg
#print axioms CubicProductSumCore.homogeneous_eq_iff

namespace CubicProductSumNormalization

theorem identity (p q u : ℝ) :
    ((5 * p + 4) * q - 27) * (135 * p + 4 * u) =
      (5 * p + 4) * ((135 * p + 4 * u) * q - u ^ 2) +
      5 * p * (u - 27) * (u + 27) + 4 * u * (u - 27) := by
  ring

theorem bound {p q u : ℝ} (hp : 0 ≤ p) (hu : 27 ≤ u)
    (hF : u ^ 2 ≤ (135 * p + 4 * u) * q) :
    27 ≤ (5 * p + 4) * q := by
  have hu0 : 0 < u := by linarith
  have hg : 0 ≤ u - 27 := sub_nonneg.mpr hu
  have hf0 : 0 ≤ (135 * p + 4 * u) * q - u ^ 2 := sub_nonneg.mpr hF
  have hd : 0 < 135 * p + 4 * u := by positivity
  have ht : 0 ≤ ((5 * p + 4) * q - 27) * (135 * p + 4 * u) := by
    rw [identity]
    positivity
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (by simpa [mul_comm] using ht) hd)

theorem equality_iff {p q u : ℝ} (hp : 0 ≤ p) (hu : 27 ≤ u)
    (hF : u ^ 2 ≤ (135 * p + 4 * u) * q) :
    (5 * p + 4) * q = 27 ↔
      u = 27 ∧ (135 * p + 4 * u) * q = u ^ 2 := by
  constructor
  · intro he
    have hu0 : 0 < u := by linarith
    have hg : 0 ≤ u - 27 := sub_nonneg.mpr hu
    have hf0 : 0 ≤ (135 * p + 4 * u) * q - u ^ 2 := sub_nonneg.mpr hF
    have h1 : 0 ≤ (5 * p + 4) * ((135 * p + 4 * u) * q - u ^ 2) := by
      positivity
    have h2 : 0 ≤ 5 * p * (u - 27) * (u + 27) := by positivity
    have hid := identity p q u
    rw [he, sub_self, zero_mul] at hid
    have hn : 4 * u * (u - 27) ≤ 0 := by linarith only [hid, h1, h2]
    have hu27 : u = 27 := by nlinarith
    refine ⟨hu27, ?_⟩
    rw [hu27]
    nlinarith only [he]
  · rintro ⟨rfl, he⟩
    nlinarith only [he]

#print axioms CubicProductSumNormalization.identity
#print axioms CubicProductSumNormalization.bound
#print axioms CubicProductSumNormalization.equality_iff

end CubicProductSumNormalization


namespace CubicProductSumInequality

def value (a b c : ℝ) : ℝ :=
  (5 * a * b * c + 4) * (a ^ 3 + b ^ 3 + c ^ 3)

theorem sum_cube_ge (a b c : ℝ) (hs : 3 ≤ a + b + c) :
    27 ≤ (a + b + c) ^ 3 := by
  calc
    27 = (3 : ℝ) ^ 3 := by norm_num
    _ ≤ (a + b + c) ^ 3 := by gcongr

theorem normalized_homogeneous (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((a + b + c) ^ 3) ^ 2 ≤
      (135 * (a * b * c) + 4 * (a + b + c) ^ 3) *
        (a ^ 3 + b ^ 3 + c ^ 3) := by
  convert CubicProductSumCore.homogeneous_nonneg a b c ha hb hc using 1 <;> ring

theorem scaled_bound (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 3 ≤ a + b + c) :
    27 ≤ value a b c := by
  have h := CubicProductSumNormalization.bound
    (p := a * b * c) (q := a ^ 3 + b ^ 3 + c ^ 3)
    (u := (a + b + c) ^ 3) (by positivity) (sum_cube_ge a b c hs)
    (normalized_homogeneous a b c ha hb hc)
  simpa only [value, mul_assoc] using h

theorem cubes_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < a ^ 3 + b ^ 3 + c ^ 3 := by positivity

theorem source_bound (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 3 ≤ a + b + c) :
    27 / (a ^ 3 + b ^ 3 + c ^ 3) ≤ 5 * a * b * c + 4 := by
  apply (div_le_iff₀ (cubes_pos a b c ha hb hc)).2
  exact scaled_bound a b c ha.le hb.le hc.le hs

theorem scaled_equality_iff (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 3 ≤ a + b + c) :
    value a b c = 27 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have hp : 0 ≤ a * b * c := by positivity
    have hEq := (CubicProductSumNormalization.equality_iff hp (sum_cube_ge a b c hs)
      (normalized_homogeneous a b c ha.le hb.le hc.le)).mp
      (by simpa only [value, mul_assoc] using he)
    have hcore : CubicProductSumCore.core a b c = 0 := by
      unfold CubicProductSumCore.core
      nlinarith only [hEq.2]
    obtain ⟨hab, hbc⟩ := (CubicProductSumCore.core_eq_zero_iff a b c ha hb hc).mp hcore
    subst a
    subst b
    have hc1 : c = 1 := by
      have heq : c ^ 3 = (1 : ℝ) ^ 3 := by nlinarith only [hEq.1]
      exact (pow_left_inj₀ hc.le (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp heq
    exact ⟨hc1, hc1, hc1⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [value]

theorem source_equality_iff (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 3 ≤ a + b + c) :
    5 * a * b * c + 4 = 27 / (a ^ 3 + b ^ 3 + c ^ 3) ↔
      a = 1 ∧ b = 1 ∧ c = 1 := by
  rw [eq_div_iff (ne_of_gt (cubes_pos a b c ha hb hc))]
  exact scaled_equality_iff a b c ha hb hc hs

theorem source_strict (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : 3 ≤ a + b + c)
    (hne : ¬ (a = 1 ∧ b = 1 ∧ c = 1)) :
    27 / (a ^ 3 + b ^ 3 + c ^ 3) < 5 * a * b * c + 4 := by
  exact lt_of_le_of_ne (source_bound a b c ha hb hc hs)
    (fun he => hne ((source_equality_iff a b c ha hb hc hs).mp he.symm))

theorem sharp_coefficient_iff (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → 3 ≤ a + b + c →
      27 / (a ^ 3 + b ^ 3 + c ^ 3) ≤ k * a * b * c + 4) ↔ 5 ≤ k := by
  constructor
  · intro h
    have h1 : (9 : ℝ) ≤ k + 4 := by
      convert h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        using 1 <;> norm_num
    linarith
  · intro hk a b c ha hb hc hs
    calc
      27 / (a ^ 3 + b ^ 3 + c ^ 3) ≤ 5 * a * b * c + 4 :=
        source_bound a b c ha hb hc hs
      _ ≤ k * a * b * c + 4 := by gcongr

theorem least_coefficient :
    IsLeast {k : ℝ | ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      3 ≤ a + b + c → 27 / (a ^ 3 + b ^ 3 + c ^ 3) ≤ k * a * b * c + 4} 5 := by
  refine ⟨(sharp_coefficient_iff 5).2 le_rfl, ?_⟩
  intro k hk
  exact (sharp_coefficient_iff k).1 hk

end CubicProductSumInequality

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) (hab : a + b + c >= 3) :
    5 * a * b * c + 4 ≥ 27 / (a ^ 3 + b ^ 3 + c ^ 3) := by
  exact CubicProductSumInequality.source_bound a b c ha hb hc hab

#print axioms CubicProductSumInequality.value
#print axioms CubicProductSumInequality.sum_cube_ge
#print axioms CubicProductSumInequality.normalized_homogeneous
#print axioms CubicProductSumInequality.scaled_bound
#print axioms CubicProductSumInequality.cubes_pos
#print axioms CubicProductSumInequality.source_bound
#print axioms CubicProductSumInequality.scaled_equality_iff
#print axioms CubicProductSumInequality.source_equality_iff
#print axioms CubicProductSumInequality.source_strict
#print axioms CubicProductSumInequality.sharp_coefficient_iff
#print axioms CubicProductSumInequality.least_coefficient
#print axioms solution
