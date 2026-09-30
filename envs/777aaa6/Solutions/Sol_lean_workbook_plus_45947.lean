-- Prove2me | solution 1 for lean_workbook_plus_45947
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:12:16.061922+00:00
-- url     : https://prove2.me/submissions/3055d0e7-b11e-4cab-b284-3e668aa8c601

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace CyclicFractionSupremum

def value (r a b c d : ℝ) : ℝ :=
  a / (a + r * b) + b / (b + r * c) + c / (c + r * d) + d / (d + r * a)

def attainable (r : ℝ) : Set ℝ :=
  {v | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ value r a b c d = v}

theorem reciprocal_identity (u v w z : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z) :
    3 - (1 / (1 + u) + 1 / (1 + v) + 1 / (1 + w) + 1 / (1 + z)) =
      ((u * v + u * w + u * z + v * w + v * z + w * z) +
        2 * (u * v * w + u * v * z + u * w * z + v * w * z) +
        3 * (u * v * w * z) - 1) /
      ((1 + u) * (1 + v) * (1 + w) * (1 + z)) := by
  have hu' : 1 + u ≠ 0 := ne_of_gt (by linarith)
  have hv' : 1 + v ≠ 0 := ne_of_gt (by linarith)
  have hw' : 1 + w ≠ 0 := ne_of_gt (by linarith)
  have hz' : 1 + z ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem reciprocal_bound (u v w z : ℝ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hz : 0 < z)
    (hp : 1 ≤ u * v * w * z) :
    1 / (1 + u) + 1 / (1 + v) + 1 / (1 + w) + 1 / (1 + z) < 3 := by
  have h2 : 0 < u * v + u * w + u * z + v * w + v * z + w * z := by positivity
  have h3 : 0 < u * v * w + u * v * z + u * w * z + v * w * z := by positivity
  have hn : 0 < (u * v + u * w + u * z + v * w + v * z + w * z) +
      2 * (u * v * w + u * v * z + u * w * z + v * w * z) +
      3 * (u * v * w * z) - 1 := by linarith only [h2, h3, hp]
  have hden : 0 < (1 + u) * (1 + v) * (1 + w) * (1 + z) := by positivity
  have := div_pos hn hden
  rw [← reciprocal_identity u v w z hu hv hw hz] at this
  linarith only [this]

theorem ratio_identity (r a b : ℝ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) :
    a / (a + r * b) = 1 / (1 + r * b / a) := by
  have hden : 0 < a + r * b := by positivity
  have hratio : 0 < 1 + r * b / a := by positivity
  field_simp

theorem ratio_product (r a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (r * b / a) * (r * c / b) * (r * d / c) * (r * a / d) = r ^ 4 := by
  field_simp

theorem strict_bound (r a b c d : ℝ) (hr : 1 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    value r a b c d < 3 := by
  have hr0 : 0 < r := by linarith
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr
  have hp : 1 ≤ (r * b / a) * (r * c / b) * (r * d / c) * (r * a / d) := by
    rw [ratio_product r a b c d ha hb hc hd]
    exact hr4
  dsimp [value]
  rw [ratio_identity r a b hr0 ha hb, ratio_identity r b c hr0 hb hc,
    ratio_identity r c d hr0 hc hd, ratio_identity r d a hr0 hd ha]
  exact reciprocal_bound _ _ _ _ (by positivity) (by positivity)
    (by positivity) (by positivity) hp

theorem geometric_family (r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    value r (t ^ 3) (t ^ 2) t 1 = 3 * t / (t + r) + 1 / (1 + r * t ^ 3) := by
  have h1 : 0 < t ^ 3 + r * t ^ 2 := by positivity
  have h2 : 0 < t ^ 2 + r * t := by positivity
  have h3 : 0 < t + r := by positivity
  have h4 : 0 < 1 + r * t ^ 3 := by positivity
  dsimp [value]
  field_simp
  ring

theorem near_supremum (r L : ℝ) (hr : 1 ≤ r) (hL : L < 3) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ L < value r a b c d := by
  have hr0 : 0 < r := by linarith
  have hg : 0 < 3 - L := by linarith
  let t : ℝ := 1 + 3 * r / (3 - L)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : (3 - L) * t = (3 - L) + 3 * r := by
    dsimp [t]
    field_simp
  have hprod : 0 < (3 - L) * (1 + r) := by positivity
  have hnum : L * (t + r) < 3 * t := by nlinarith only [he, hprod]
  have hfrac : L < 3 * t / (t + r) :=
    (lt_div_iff₀ (by positivity : 0 < t + r)).mpr hnum
  have hlast : 0 < 1 / (1 + r * t ^ 3) := by positivity
  refine ⟨t ^ 3, t ^ 2, t, 1, by positivity, by positivity, ht, by norm_num, ?_⟩
  rw [geometric_family r t hr0 ht]
  linarith only [hfrac, hlast]

theorem supremum (r : ℝ) (hr : 1 ≤ r) : IsLUB (attainable r) 3 := by
  constructor
  · rintro v ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩
    exact le_of_lt (strict_bound r a b c d hr ha hb hc hd)
  · intro L hL
    by_contra h
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hvalue⟩ := near_supremum r L hr (lt_of_not_ge h)
    have := hL (show value r a b c d ∈ attainable r from ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩)
    exact (not_lt_of_ge this) hvalue

theorem supremum_unattained (r : ℝ) (hr : 1 ≤ r) : 3 ∉ attainable r := by
  rintro ⟨a, b, c, d, ha, hb, hc, hd, he⟩
  have := strict_bound r a b c d hr ha hb hc hd
  linarith only [this, he]

theorem no_greatest (r v : ℝ) (hr : 1 ≤ r) : ¬ IsGreatest (attainable r) v := by
  rintro ⟨hv, hub⟩
  obtain ⟨a, b, c, d, ha, hb, hc, hd, he⟩ := hv
  have hv3 : v < 3 := he ▸ strict_bound r a b c d hr ha hb hc hd
  have h3v : 3 ≤ v := (supremum r hr).2 hub
  exact (not_lt_of_ge h3v) hv3

theorem source_supremum : IsLUB (attainable 3) 3 := supremum 3 (by norm_num)

end CyclicFractionSupremum

theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a / (a + 3 * b) + b / (b + 3 * c) + c / (c + 3 * d) + d / (d + 3 * a) < 3 := by
  exact CyclicFractionSupremum.strict_bound 3 a b c d (by norm_num) ha hb hc hd

#print axioms CyclicFractionSupremum.reciprocal_identity
#print axioms CyclicFractionSupremum.reciprocal_bound
#print axioms CyclicFractionSupremum.ratio_identity
#print axioms CyclicFractionSupremum.ratio_product
#print axioms CyclicFractionSupremum.strict_bound
#print axioms CyclicFractionSupremum.geometric_family
#print axioms CyclicFractionSupremum.near_supremum
#print axioms CyclicFractionSupremum.supremum
#print axioms CyclicFractionSupremum.supremum_unattained
#print axioms CyclicFractionSupremum.no_greatest
#print axioms CyclicFractionSupremum.source_supremum
#print axioms solution
