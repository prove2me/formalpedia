-- Prove2me | solution 1 for AttentionBudget.tail_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:19:49.042864+00:00
-- url     : https://prove2.me/submissions/210f9eb7-c518-440e-8e58-e3c82ae366d4

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_headMass_mono

open AttentionBudget
open Finset

/-- A profile with decay ratio `r` is dominated by the geometric profile `w 0 * r ^ i`. -/
lemma weight_le_geometric' {w : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r)
    (hdec : ∀ i, w (i + 1) ≤ r * w i) : ∀ i, w i ≤ w 0 * r ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ m ih =>
      calc w (m + 1) ≤ r * w m := hdec m
        _ ≤ r * (w 0 * r ^ m) := by exact mul_le_mul_of_nonneg_left ih hr0
        _ = w 0 * r ^ (m + 1) := by ring

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {r τ : ℝ}

open AttentionBudget in
lemma solution (hr0 : 0 < r) (hr1 : r < 1) (hdec : ∀ i, w (i + 1) ≤ r * w i)
    (hw : ∀ i, 0 < w i) (k n : ℕ) :
    headMass w n - headMass w k ≤ w 0 * r ^ k / (1 - r) := by
  have hr1' : (0 : ℝ) < 1 - r := by linarith
  have hw0 : 0 < w 0 := hw 0
  rcases le_or_gt n k with hnk | hkn
  · have : headMass w n ≤ headMass w k := headMass_mono hw hnk
    have : (0 : ℝ) ≤ w 0 * r ^ k / (1 - r) :=
      div_nonneg (mul_nonneg hw0.le (pow_nonneg hr0.le k)) hr1'.le
    linarith [headMass_mono hw hnk]
  · have hsub : headMass w n - headMass w k = ∑ i ∈ Finset.Ico k n, w i := by
      rw [Finset.sum_Ico_eq_sub _ hkn.le]
      simp [headMass]
    have hbound : ∑ i ∈ Finset.Ico k n, w i ≤ ∑ i ∈ Finset.Ico k n, w 0 * r ^ i :=
      Finset.sum_le_sum fun i _ => weight_le_geometric' hr0.le hdec i
    have hgeom : ∑ i ∈ Finset.Ico k n, w 0 * r ^ i = w 0 * ((r ^ n - r ^ k) / (r - 1)) := by
      rw [← Finset.mul_sum, geom_sum_Ico (by linarith) hkn.le]
    have hkey : w 0 * ((r ^ n - r ^ k) / (r - 1)) ≤ w 0 * r ^ k / (1 - r) := by
      have hrn : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0.le n
      have hne1 : (1 : ℝ) - r ≠ 0 := hr1'.ne'
      have hne2 : r - 1 ≠ 0 := fun h => hne1 (by linarith)
      have : (r ^ n - r ^ k) / (r - 1) = (r ^ k - r ^ n) / (1 - r) := by
        field_simp
        ring
      rw [this, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ hr1'.le |>.trans_eq rfl
      nlinarith
    rw [hsub]
    calc ∑ i ∈ Finset.Ico k n, w i ≤ ∑ i ∈ Finset.Ico k n, w 0 * r ^ i := hbound
      _ = w 0 * ((r ^ n - r ^ k) / (r - 1)) := hgeom
      _ ≤ w 0 * r ^ k / (1 - r) := hkey
