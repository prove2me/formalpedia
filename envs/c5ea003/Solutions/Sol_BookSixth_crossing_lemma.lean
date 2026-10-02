-- Prove2me | solution 1 for BookSixth.crossing_lemma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T11:43:10.165725+00:00
-- url     : https://prove2.me/submissions/a774c489-bcc9-4ca6-9557-587d3b27f3db

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_drawing_sampling_bound
open scoped BigOperators
open BookSixth

theorem solution {N M : ℕ} (hN : 0 < N) (hM : 4*N ≤ M) (D : PlaneDrawing N M) :
    M^3 ≤ 64 * N^2 * D.crossings.card := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hmNat : 0 < M := by omega
  have hm : (0 : ℝ) < M := by exact_mod_cast hmNat
  have hnm : (4 : ℝ) * N ≤ M := by exact_mod_cast hM
  let p : ℝ := 4 * (N : ℝ) / M
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact (div_le_one hm).mpr hnm
  have h := BookSixth.drawing_sampling_bound D p hp hp1
  have hid : (M : ℝ)^4 *
      (p^2 * M - (3*p*N + p^4*(D.crossings.card : ℝ))) =
      4*(N : ℝ)^2*((M : ℝ)^3 - 64*(N : ℝ)^2*(D.crossings.card : ℝ)) := by
    dsimp [p]
    field_simp [ne_of_gt hm]
    <;> ring
  have hs : 4*(N : ℝ)^2*((M : ℝ)^3 - 64*(N : ℝ)^2*(D.crossings.card : ℝ)) ≤ 0 := by
    rw [← hid]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr h)
  have hfactor : (0 : ℝ) < 4*(N : ℝ)^2 := by positivity
  have hbound : (M : ℝ)^3 ≤ 64*(N : ℝ)^2*(D.crossings.card : ℝ) := by
    by_contra hnot
    have hd : 0 < (M : ℝ)^3 - 64*(N : ℝ)^2*(D.crossings.card : ℝ) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hc := mul_pos hfactor hd
    linarith
  exact_mod_cast hbound
