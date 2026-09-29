-- Prove2me | solution 2 for EscapeCriterion.escape_time_loglog
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:00:48.222131+00:00
-- url     : https://prove2.me/submissions/bb5a1842-4641-42a9-b34c-fe1bade2cf67

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateGreenFunction
open EscapeCriterion in
theorem solution {c z : ℂ} (hz : escapeRadius c < ‖z‖) (h3 : 3 ≤ ‖z‖) {B : ℝ} (hB : 0 < B)
    {n : ℕ} (hn : (Real.log B - 1) / (Real.log ‖z‖ - 1) ≤ 2 ^ n) : B ≤ ‖orbit c z n‖ := by
  have hR2 : ∀ c : ℂ, 2 ≤ escapeRadius c := fun c => le_max_left _ _
  have hRc : ∀ c : ℂ, ‖c‖ ≤ escapeRadius c := fun c => le_max_right _ _
  have hgrow : ∀ (c w : ℂ), escapeRadius c < ‖w‖ →
      ‖w‖ * (‖w‖ - 1) ≤ ‖MandelbrotEscape.qmap c w‖ := by
    intro c w hw
    have h := norm_sub_le (w ^ 2 + c) c
    simp only [add_sub_cancel_right, norm_pow] at h
    have := hRc c
    unfold MandelbrotEscape.qmap
    nlinarith
  have hgrowth : ∀ (c z : ℂ), escapeRadius c < ‖z‖ → ∀ n, escapeRadius c < ‖orbit c z n‖ ∧
      ‖z‖ ≤ ‖orbit c z n‖ ∧ (‖z‖ - 1) ^ n * ‖z‖ ≤ ‖orbit c z n‖ := by
    intro c z hz n
    induction n with
    | zero => simp [orbit, hz]
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hs : orbit c z (n + 1) = MandelbrotEscape.qmap c (orbit c z n) :=
        Function.iterate_succ_apply' _ _ _
      have hg := hgrow c _ h1
      have hR := hR2 c
      rw [hs]
      refine ⟨by nlinarith, by nlinarith, ?_⟩
      have hz1 : 0 ≤ ‖z‖ - 1 := by linarith
      have hp : 0 ≤ (‖z‖ - 1) ^ n * ‖z‖ := mul_nonneg (pow_nonneg hz1 n) (norm_nonneg z)
      calc (‖z‖ - 1) ^ (n + 1) * ‖z‖ = (‖z‖ - 1) * ((‖z‖ - 1) ^ n * ‖z‖) := by ring
        _ ≤ (‖orbit c z n‖ - 1) * ‖orbit c z n‖ :=
            mul_le_mul (by linarith) h3 hp (by linarith)
        _ = ‖orbit c z n‖ * (‖orbit c z n‖ - 1) := by ring
        _ ≤ _ := hg
  have hstep : ∀ n : ℕ, |Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖| ≤ 2 / ‖orbit c z n‖ := by
    intro n
    have h1 := (hgrowth c z hz n).1
    have hs : orbit c z (n + 1) = MandelbrotEscape.qmap c (orbit c z n) :=
      Function.iterate_succ_apply' _ _ _
    have hcR := hRc c
    have hR := hR2 c
    have hup : ‖orbit c z (n + 1)‖ ≤ ‖orbit c z n‖ ^ 2 + ‖c‖ := by
      rw [hs]
      unfold MandelbrotEscape.qmap
      calc ‖orbit c z n ^ 2 + c‖ ≤ ‖orbit c z n ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖orbit c z n‖ ^ 2 + ‖c‖ := by rw [norm_pow]
    have hlo : ‖orbit c z n‖ ^ 2 - ‖c‖ ≤ ‖orbit c z (n + 1)‖ := by
      rw [hs]
      unfold MandelbrotEscape.qmap
      have h := norm_sub_le (orbit c z n ^ 2 + c) c
      simp only [add_sub_cancel_right, norm_pow] at h
      linarith
    generalize ‖orbit c z (n + 1)‖ = a at hup hlo ⊢
    generalize ‖orbit c z n‖ = w at h1 hup hlo ⊢
    have hw2 : 2 < w := by linarith
    have hwpos : 0 < w := by linarith
    have hapos : 0 < a := by nlinarith
    have hw2pos : 0 < w ^ 2 := by positivity
    have hlog : Real.log a - 2 * Real.log w = Real.log (a / w ^ 2) := by
      rw [Real.log_div hapos.ne' hw2pos.ne', Real.log_pow]
      push_cast
      ring
    rw [hlog]
    have hxpos : 0 < a / w ^ 2 := div_pos hapos hw2pos
    have hxup : a / w ^ 2 ≤ 1 + 1 / w := by
      rw [div_le_iff₀ hw2pos]
      have : (1 + 1 / w) * w ^ 2 = w ^ 2 + w := by field_simp
      rw [this]
      linarith
    have hxlo : (w - 1) / w ≤ a / w ^ 2 := by
      rw [div_le_div_iff₀ hwpos hw2pos]
      nlinarith
    rw [abs_le]
    constructor
    · have hl := Real.one_sub_inv_le_log_of_pos hxpos
      have hy : (a / w ^ 2)⁻¹ ≤ w / (w - 1) := by
        rw [inv_le_comm₀ hxpos (by apply div_pos hwpos; linarith), inv_div]
        exact hxlo
      have hq : w / (w - 1) ≤ 1 + 2 / w := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < w - 1)]
        have : (1 + 2 / w) * (w - 1) = w + 1 - 2 / w := by field_simp; ring
        rw [this]
        have : 2 / w ≤ 1 := by rw [div_le_one hwpos]; linarith
        linarith
      have : -(2 / w) ≤ 1 - (a / w ^ 2)⁻¹ := by linarith
      linarith
    · have hl := Real.log_le_sub_one_of_pos hxpos
      have : 1 / w ≤ 2 / w := by
        apply div_le_div_of_nonneg_right (by norm_num) hwpos.le
      linarith
  have hlogG : ∀ m : ℕ, 2 ^ m * (Real.log ‖z‖ - 1) ≤ Real.log ‖orbit c z m‖ - 1 := by
    intro m
    induction m with
    | zero => simp [orbit]
    | succ m ih =>
      have h := (abs_le.mp (hstep m)).1
      have hw := (hgrowth c z hz m).1
      have hR := hR2 c
      have hwpos : 0 < ‖orbit c z m‖ := by linarith
      have h2w : 2 / ‖orbit c z m‖ ≤ 1 := by
        rw [div_le_one hwpos]
        linarith
      rw [pow_succ]
      nlinarith
  have hlog3 : 1 < Real.log ‖z‖ := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hpos : 0 < Real.log ‖z‖ - 1 := by linarith
  have h1 : Real.log B - 1 ≤ 2 ^ n * (Real.log ‖z‖ - 1) := by
    rwa [div_le_iff₀ hpos] at hn
  have h2 := hlogG n
  have hopos : 0 < ‖orbit c z n‖ := by
    have := (hgrowth c z hz n).1
    have := hR2 c
    linarith
  have hlog : Real.log B ≤ Real.log ‖orbit c z n‖ := by linarith
  exact (Real.log_le_log_iff hB hopos).mp hlog
