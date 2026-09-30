-- Prove2me | solution 1 for lean_workbook_plus_33727
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:46:50.657761+00:00
-- url     : https://prove2.me/submissions/75ea7a75-57b2-42bd-b582-9d3c2e6b901a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace WeightedPairMeanReconstruction

noncomputable def mean (x y : ℝ) : ℝ := (1 / 3) * min x y + (2 / 3) * max x y

theorem mean_comm (x y : ℝ) : mean x y = mean y x := by
  simp only [mean, min_comm, max_comm]

theorem three_mul_mean (x y : ℝ) : 3 * mean x y = x + y + max x y := by
  have h := min_add_max x y
  unfold mean
  linarith only [h]

theorem strictMono_left (z : ℝ) : StrictMono (fun x => mean x z) := by
  intro x y hxy
  have hm : max x z ≤ max y z := max_le_max hxy.le le_rfl
  linarith only [three_mul_mean x z, three_mul_mean y z, hm, hxy]

theorem coordinate_order (z x y : ℝ) : mean x z ≤ mean y z ↔ x ≤ y :=
  (strictMono_left z).le_iff_le

theorem ordered_coordinates {p q r x y z : ℝ} (hpq : p ≤ q) (hqr : q ≤ r)
    (h1 : mean x y = p) (h2 : mean y z = q) (h3 : mean z x = r) :
    y ≤ x ∧ x ≤ z := by
  constructor
  · apply (coordinate_order z y x).mp
    rw [h2, mean_comm x z, h3]
    exact hqr
  · apply (coordinate_order y x z).mp
    rw [h1, mean_comm z y, h2]
    exact hpq

theorem ordered_classification {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r)
    (x y z : ℝ) :
    (mean x y = p ∧ mean y z = q ∧ mean z x = r) ↔
      x = p + r - q ∧ y = p + 2 * q - 2 * r ∧ z = (-p + q + 2 * r) / 2 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨hyx, hxz⟩ := ordered_coordinates hpq hqr h1 h2 h3
    dsimp [mean] at h1 h2 h3
    rw [min_eq_right hyx, max_eq_left hyx] at h1
    rw [min_eq_left (hyx.trans hxz), max_eq_right (hyx.trans hxz)] at h2
    rw [min_eq_right hxz, max_eq_left hxz] at h3
    exact ⟨by linarith only [h1, h2, h3],
      by linarith only [h1, h2, h3], by linarith only [h1, h2, h3]⟩
  · rintro ⟨hx, hy, hz⟩
    have hyx : y ≤ x := by linarith only [hqr, hx, hy]
    have hxz : x ≤ z := by linarith only [hpq, hx, hz]
    refine ⟨?_, ?_, ?_⟩
    · simp only [mean, min_eq_right hyx, max_eq_left hyx]
      linarith only [hx, hy]
    · simp only [mean, min_eq_left (hyx.trans hxz), max_eq_right (hyx.trans hxz)]
      linarith only [hy, hz]
    · simp only [mean, min_eq_right hxz, max_eq_left hxz]
      linarith only [hx, hz]

theorem ordered_model {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) :
    mean (p + r - q) (p + 2 * q - 2 * r) = p ∧
      mean (p + 2 * q - 2 * r) ((-p + q + 2 * r) / 2) = q ∧
      mean ((-p + q + 2 * r) / 2) (p + r - q) = r :=
  (ordered_classification hpq hqr _ _ _).mpr ⟨rfl, rfl, rfl⟩

theorem ordered_unique {p q r : ℝ} (hpq : p ≤ q) (hqr : q ≤ r) :
    ∃! v : ℝ × ℝ × ℝ,
      mean v.1 v.2.1 = p ∧ mean v.2.1 v.2.2 = q ∧ mean v.2.2 v.1 = r := by
  refine ⟨(p + r - q, p + 2 * q - 2 * r, (-p + q + 2 * r) / 2),
    ordered_model hpq hqr, ?_⟩
  intro v hv
  obtain ⟨hx, hy, hz⟩ := (ordered_classification hpq hqr v.1 v.2.1 v.2.2).mp hv
  exact Prod.ext hx (Prod.ext hy hz)

theorem source_classification (x y z : ℝ) :
    (mean x y = 2017 ∧ mean y z = 2018 ∧ mean z x = 2019) ↔
      x = 2018 ∧ y = 2015 ∧ z = 2019.5 := by
  convert ordered_classification (p := 2017) (q := 2018) (r := 2019)
    (by norm_num) (by norm_num) x y z using 1
  norm_num
  rfl

end WeightedPairMeanReconstruction

theorem solution (x y z : ℝ) :
    (x = 2018 ∧ y = 2015 ∧ z = 2019.5 ↔
      1 / 3 * min x y + 2 / 3 * max x y = 2017 ∧
      1 / 3 * min y z + 2 / 3 * max y z = 2018 ∧
      1 / 3 * min z x + 2 / 3 * max z x = 2019) := by
  exact (WeightedPairMeanReconstruction.source_classification x y z).symm
