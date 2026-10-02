-- Prove2me | solution 2 for BookSixth.crossing_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:02:32.680767+00:00
-- url     : https://prove2.me/submissions/bc4bfe5c-9501-4327-aac8-c701789bc09d

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_drawing_sampling_bound

open scoped BigOperators
open BookSixth

/-! The crossing lemma from the sampling bound, at `p = 4N/M`. -/

private lemma key_arith (n m X : ℝ) (hn : 0 < n) (hm : 4 * n ≤ m) (hX : 0 ≤ X)
    (h : (4 * n / m) ^ 2 * m ≤ 3 * (4 * n / m) * n + (4 * n / m) ^ 4 * X) :
    m ^ 3 ≤ 64 * n ^ 2 * X := by
  have hm0 : 0 < m := by linarith
  have hmne : m ≠ 0 := ne_of_gt hm0
  field_simp at h
  linarith

theorem _root_.solution {N M : ℕ} (hN : 0 < N) (hM : 4 * N ≤ M) (D : PlaneDrawing N M) :
    M ^ 3 ≤ 64 * N ^ 2 * D.crossings.card := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMR : (4 : ℝ) * (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
  have hp0 : (0 : ℝ) ≤ 4 * (N : ℝ) / (M : ℝ) := by positivity
  have hp1 : 4 * (N : ℝ) / (M : ℝ) ≤ 1 := by rw [div_le_one hM0]; linarith
  have hb := BookSixth.drawing_sampling_bound D (4 * (N : ℝ) / (M : ℝ)) hp0 hp1
  have hX0 : (0 : ℝ) ≤ ((D.crossings.card : ℕ) : ℝ) := by positivity
  have hkey := key_arith (N : ℝ) (M : ℝ) ((D.crossings.card : ℕ) : ℝ) hNR hMR hX0 hb
  exact_mod_cast hkey

#print axioms solution
