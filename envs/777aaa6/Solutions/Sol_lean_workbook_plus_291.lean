-- Prove2me | solution 1 for lean_workbook_plus_291
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:56.879891+00:00
-- url     : https://prove2.me/submissions/a6807ac1-34c0-4ca9-abec-9cfb6e9ae4b5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem eigenvalue_abs_le_one {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (hsum : ∀ i, ∑ j, a i j = 1)
    (v : Fin n → ℝ) (hv : v ≠ 0) (l : ℝ) (heig : a.mulVec v = l • v) :
    |l| ≤ 1 := by
  classical
  have hex : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨j, hj⟩ := hex
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun k => |v k|)
    ⟨j, Finset.mem_univ j⟩
  have hi : 0 < |v i| := lt_of_lt_of_le (abs_pos.mpr hj) (hmax j (Finset.mem_univ j))
  have heigi := congrFun heig i
  change (∑ k, a i k * v k) = l * v i at heigi
  have hb : |l| * |v i| ≤ 1 * |v i| := by
    calc
      |l| * |v i| = |∑ k, a i k * v k| := by rw [← abs_mul, ← heigi]
      _ ≤ ∑ k, |a i k * v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, a i k * |v i| := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (ha i k)]
        exact mul_le_mul_of_nonneg_left (hmax k hk) (ha i k)
      _ = 1 * |v i| := by rw [← Finset.sum_mul, hsum i]
  exact le_of_mul_le_mul_right hb hi

theorem solution (n : ℕ) (hn : 0 < n) (a : Matrix (Fin n) (Fin n) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (h : ∀ i, ∑ j, a i j = 1)
    (a_eig : ∃ v : Fin n → ℝ, ∃ l : ℝ, a.mulVec v = l • v) :
    ∃ v : Fin n → ℝ, ∃ l : ℝ, a.mulVec v = l • v ∧ l ≤ 1 ∧ -1 ≤ l := by
  let v : Fin n → ℝ := fun _ => 1
  have hv : v ≠ 0 := by
    intro hz
    have hi := congrFun hz ⟨0, hn⟩
    norm_num [v] at hi
  have heig : a.mulVec v = (1 : ℝ) • v := by
    ext i
    change (∑ j, a i j * 1) = 1 * 1
    simpa using h i
  have hb := eigenvalue_abs_le_one a ha h v hv 1 heig
  exact ⟨v, 1, heig, (abs_le.mp hb).2, (abs_le.mp hb).1⟩
