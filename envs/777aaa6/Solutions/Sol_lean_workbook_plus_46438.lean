-- Prove2me | solution 1 for lean_workbook_plus_46438
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:01:38.583291+00:00
-- url     : https://prove2.me/submissions/278be63c-888b-4640-8532-ce95ff47f7e6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace DividedDifferenceProductClassification

def Satisfies (f : ℝ → ℝ) : Prop :=
  ∀ x y z : ℝ, x ≠ y → y ≠ z → z ≠ x →
    f x * f y * f z = f x / (x - y) / (x - z) +
      f y / (y - x) / (y - z) + f z / (z - x) / (z - y)

theorem zero_satisfies : Satisfies (fun _ => 0) := by
  intro x y z hxy hyz hzx
  simp

theorem cleared_identity {f : ℝ → ℝ} (hf : Satisfies f)
    {x y : ℝ} (hxy : x ≠ y) (z : ℝ) :
    (f x * f y * (x - z) * (y - z) - 1) * (x - y) * f z =
      f x * (y - z) - f y * (x - z) := by
  by_cases hzx : z = x
  · subst z
    ring
  by_cases hzy : z = y
  · subst z
    ring
  have h := hf x y z hxy (Ne.symm hzy) hzx
  rw [show y - x = -(x - y) by ring,
    show z - x = -(x - z) by ring,
    show z - y = -(y - z) by ring] at h
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr (Ne.symm hzx),
    sub_ne_zero.mpr (Ne.symm hzy)] at h
  nlinarith only [h]

theorem pair_product_nonpos {f : ℝ → ℝ} (hf : Satisfies f)
    {x y : ℝ} (hxy : x ≠ y) : f x * f y ≤ 0 := by
  by_contra h
  have hs : 0 < f x * f y := lt_of_not_ge h
  let t : ℝ := 1 / (f x * f y)
  have ht : 0 < t := one_div_pos.mpr hs
  have hst : f x * f y * t = 1 := by
    dsimp [t]
    exact mul_one_div_cancel (ne_of_gt hs)
  have hD : 0 < (x - y) ^ 2 + 4 * t := by
    nlinarith only [sq_nonneg (x - y), ht]
  let r := Real.sqrt ((x - y) ^ 2 + 4 * t)
  have hr : 0 < r := Real.sqrt_pos.mpr hD
  have hr2 : r ^ 2 = (x - y) ^ 2 + 4 * t := Real.sq_sqrt (le_of_lt hD)
  let u := (x + y + r) / 2
  let v := (x + y - r) / 2
  have huv : u ≠ v := by
    dsimp [u, v]
    linarith only [hr]
  have hu_root : (x - u) * (y - u) = t := by
    dsimp [u]
    nlinarith only [hr2]
  have hv_root : (x - v) * (y - v) = t := by
    dsimp [v]
    nlinarith only [hr2]
  have hu_prod : f x * f y * (x - u) * (y - u) = 1 := by
    calc
      _ = f x * f y * ((x - u) * (y - u)) := by ring
      _ = 1 := by rw [hu_root, hst]
  have hv_prod : f x * f y * (x - v) * (y - v) = 1 := by
    calc
      _ = f x * f y * ((x - v) * (y - v)) := by ring
      _ = 1 := by rw [hv_root, hst]
  have hu := cleared_identity hf hxy u
  have hv := cleared_identity hf hxy v
  rw [hu_prod] at hu
  rw [hv_prod] at hv
  simp only [sub_self, zero_mul] at hu hv
  have hdiff : (f x - f y) * (u - v) = 0 := by
    nlinarith only [hu, hv]
  have hsame : f x = f y := sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr huv))
  rw [hsame] at hu
  have hyzero : f y * (x - y) = 0 := by nlinarith only [hu]
  have hfy : f y = 0 :=
    (mul_eq_zero.mp hyzero).resolve_right (sub_ne_zero.mpr hxy)
  rw [hfy, mul_zero] at hs
  exact (lt_irrefl 0) hs

private theorem one_of_three_zero (a b c : ℝ)
    (hab : a * b ≤ 0) (hac : a * c ≤ 0) (hbc : b * c ≤ 0) :
    a = 0 ∨ b = 0 ∨ c = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr (Or.inl hb)
  by_cases hc : c = 0
  · exact Or.inr (Or.inr hc)
  have hab' : a * b < 0 := lt_of_le_of_ne hab (mul_ne_zero ha hb)
  have hac' : a * c < 0 := lt_of_le_of_ne hac (mul_ne_zero ha hc)
  have hp := mul_pos_of_neg_of_neg hab' hac'
  have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hbc
  exfalso
  nlinarith only [hp, hn]

theorem exists_zero {f : ℝ → ℝ} (hf : Satisfies f) : ∃ a : ℝ, f a = 0 := by
  have h := one_of_three_zero (f 0) (f 1) (f 2)
    (pair_product_nonpos hf (by norm_num : (0 : ℝ) ≠ 1))
    (pair_product_nonpos hf (by norm_num : (0 : ℝ) ≠ 2))
    (pair_product_nonpos hf (by norm_num : (1 : ℝ) ≠ 2))
  rcases h with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem eq_linear_of_zero {f : ℝ → ℝ} (hf : Satisfies f)
    {a : ℝ} (ha : f a = 0) (x : ℝ) : f x = f (a + 1) * (x - a) := by
  have h := cleared_identity hf (show a ≠ a + 1 by linarith) x
  rw [ha] at h
  nlinarith only [h]

theorem eq_zero {f : ℝ → ℝ} (hf : Satisfies f) : f = fun _ => 0 := by
  obtain ⟨a, ha⟩ := exists_zero hf
  have h := pair_product_nonpos hf (show a + 1 ≠ a + 2 by linarith)
  rw [eq_linear_of_zero hf ha (a + 2)] at h
  have hm : f (a + 1) = 0 := by nlinarith only [h, sq_nonneg (f (a + 1))]
  funext x
  rw [eq_linear_of_zero hf ha x, hm, zero_mul]

theorem classification (f : ℝ → ℝ) : Satisfies f ↔ f = fun _ => 0 := by
  constructor
  · exact eq_zero
  · rintro rfl
    exact zero_satisfies

theorem unique_solution : ∃! f : ℝ → ℝ, Satisfies f := by
  refine ⟨fun _ => 0, zero_satisfies, ?_⟩
  intro f hf
  exact eq_zero hf

end DividedDifferenceProductClassification

theorem solution (x y z : ℝ) (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) :
    ∃ f : ℝ → ℝ, f x * f y * f z = f x / (x - y) / (x - z) +
      f y / (y - x) / (y - z) + f z / (z - x) / (z - y) := by
  obtain ⟨f, hf, _⟩ := DividedDifferenceProductClassification.unique_solution
  exact ⟨f, hf x y z h.1 h.2.1 h.2.2⟩
