-- Prove2me | solution 1 for EscapeCriterion.escapeRate_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:25:48.967815+00:00
-- url     : https://prove2.me/submissions/1b25ad1d-6d01-4fbe-9dd4-fd9698d62302

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
open EscapeCriterion in
theorem solution {c z : ℂ} (hz : escapeRadius c < ‖z‖) : 0 < escapeRate c z := by
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
  have hstepG : ∀ z : ℂ, escapeRadius c < ‖z‖ → ∀ n : ℕ, |Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖| ≤ 2 / ‖orbit c z n‖ := by
    intro z hz n
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
  have htend : ∀ (c z : ℂ), escapeRadius c < ‖z‖ →
      Filter.Tendsto (fun n => ‖orbit c z n‖) Filter.atTop Filter.atTop := by
    intro c z hz
    have hz1 : 1 < ‖z‖ - 1 := by linarith [hR2 c]
    have hpow := tendsto_pow_atTop_atTop_of_one_lt hz1
    refine Filter.tendsto_atTop_mono (fun n => ?_) hpow
    have hn := (hgrowth c z hz n).2.2
    have hp : 0 ≤ (‖z‖ - 1) ^ n := pow_nonneg (by linarith) n
    calc (‖z‖ - 1) ^ n ≤ (‖z‖ - 1) ^ n * ‖z‖ := le_mul_of_one_le_right hp (by linarith)
      _ ≤ _ := hn
  have hshift : ∀ (c z : ℂ) (N n : ℕ), orbit c (orbit c z N) n = orbit c z (n + N) := by
    intro c z N n
    unfold orbit
    rw [Function.iterate_add_apply]
  have htend' : ∀ (c z : ℂ), (∃ N, escapeRadius c < ‖orbit c z N‖) →
      Filter.Tendsto (fun n => ‖orbit c z n‖) Filter.atTop Filter.atTop := by
    rintro c z ⟨N, hN⟩
    have h := htend c _ hN
    simp only [hshift] at h
    exact (Filter.tendsto_add_atTop_iff_nat N).mp h
  have hlogG : ∀ u : ℂ, escapeRadius c < ‖u‖ → ∀ m : ℕ,
      2 ^ m * (Real.log ‖u‖ - 1) ≤ Real.log ‖orbit c u m‖ - 1 := by
    intro u hu m
    induction m with
    | zero => simp [orbit]
    | succ m ih =>
      have h := (abs_le.mp (hstepG u hu m)).1
      have hw := (hgrowth c u hu m).1
      have hR := hR2 c
      have hwpos : 0 < ‖orbit c u m‖ := by linarith
      have h2w : 2 / ‖orbit c u m‖ ≤ 1 := by
        rw [div_le_one hwpos]
        linarith
      rw [pow_succ]
      nlinarith
  have hdist : ∀ n : ℕ, dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ 1 / 2 / 2 ^ n := by
    intro n
    have h := hstepG z hz n
    have hw := (hgrowth c z hz n).1
    have hR := hR2 c
    have hwpos : 0 < ‖orbit c z n‖ := by linarith
    have h2w : 2 / ‖orbit c z n‖ ≤ 1 := by
      rw [div_le_one hwpos]
      linarith
    rw [Real.dist_eq]
    unfold logOrbitSeq
    have heq : Real.log ‖orbit c z n‖ / 2 ^ n - Real.log ‖orbit c z (n + 1)‖ / 2 ^ (n + 1)
        = -((Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖) / 2 ^ (n + 1)) := by
      rw [pow_succ]
      field_simp
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (n + 1))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (n + 1))]
    have hone : (1 : ℝ) / 2 / 2 ^ n * 2 ^ (n + 1) = 1 := by
      rw [pow_succ]
      have : (2 : ℝ) ^ n ≠ 0 := by positivity
      field_simp
    rw [hone]
    linarith
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two hdist)
  have hlim : Filter.Tendsto (logOrbitSeq c z) Filter.atTop (nhds (escapeRate c z)) :=
    tendsto_nhds_limUnder ⟨l, hl⟩
  obtain ⟨N, hN⟩ := ((htend c z hz).eventually_ge_atTop (Real.exp 2)).exists
  have hNesc : escapeRadius c < ‖orbit c z N‖ := (hgrowth c z hz N).1
  have hlogN : 2 ≤ Real.log ‖orbit c z N‖ := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos 2])]
    exact hN
  have hshift : ∀ m, orbit c (orbit c z N) m = orbit c z (m + N) := by
    intro m
    unfold orbit
    rw [Function.iterate_add_apply]
  have hev : ∀ᶠ n in Filter.atTop, 1 / 2 ^ N ≤ logOrbitSeq c z n := by
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
    have hg := hlogG _ hNesc m
    rw [hshift] at hg
    have hge : (2 : ℝ) ^ m ≤ Real.log ‖orbit c z (m + N)‖ := by
      have : (2 : ℝ) ^ m * 1 ≤ 2 ^ m * (Real.log ‖orbit c z N‖ - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    unfold logOrbitSeq
    rw [le_div_iff₀ (by positivity), pow_add]
    have : (1 : ℝ) / 2 ^ N * (2 ^ m * 2 ^ N) = 2 ^ m := by
      have : (2 : ℝ) ^ N ≠ 0 := by positivity
      field_simp
    rw [this]
    exact hge
  have hge := ge_of_tendsto hlim hev
  have hpos : (0 : ℝ) < 1 / 2 ^ N := by positivity
  linarith
