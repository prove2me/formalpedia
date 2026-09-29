-- Prove2me | solution 2 for EscapeCriterion.continuousOn_mandelbrotPotential
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:17:50.06486+00:00
-- url     : https://prove2.me/submissions/58e06672-b344-4698-a3c8-e490a656d172

import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_FilledJuliaCompact
open EscapeCriterion in
theorem solution : ContinuousOn mandelbrotPotential {c : ℂ | 2 < ‖c‖} := by
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
  have hc2G : ∀ c : ℂ, 2 < ‖c‖ → escapeRadius c < ‖orbit c 0 2‖ := by
    intro c hc
    have hR : escapeRadius c = ‖c‖ := max_eq_right hc.le
    have h2 : orbit c 0 2 = c ^ 2 + c := by
      simp [orbit, MandelbrotEscape.qmap]
    rw [hR, h2]
    have h := norm_sub_le (c ^ 2 + c) c
    simp only [add_sub_cancel_right, norm_pow] at h
    nlinarith
  have hcontO : ∀ k : ℕ, Continuous (fun c : ℂ => orbit c 0 k) := by
    intro k
    induction k with
    | zero => simpa [orbit] using continuous_const
    | succ k ih =>
      have heq : (fun c : ℂ => orbit c 0 (k + 1)) = fun c => (orbit c 0 k) ^ 2 + c := by
        funext c
        exact Function.iterate_succ_apply' _ _ _
      rw [heq]
      exact (ih.pow 2).add continuous_id
  have hshift : ∀ (c : ℂ) (m : ℕ), orbit c (orbit c 0 2) m = orbit c 0 (m + 2) := by
    intro c m
    unfold orbit
    rw [Function.iterate_add_apply]
  have hcont : ∀ n : ℕ, ContinuousOn (potentialSeq n) {c : ℂ | 2 < ‖c‖} := by
    intro n
    have hne : ∀ c ∈ {c : ℂ | 2 < ‖c‖}, ‖orbit c 0 (n + 2)‖ ≠ 0 := by
      intro c hc
      have h1 := (hgrowth c _ (hc2G c hc) n).1
      rw [hshift] at h1
      have := hR2 c
      exact ne_of_gt (by linarith)
    have heq : potentialSeq n = fun c => Real.log ‖orbit c 0 (n + 2)‖ / 2 ^ n / 2 := by
      funext c
      unfold potentialSeq logOrbitSeq
      rw [hshift]
    rw [heq]
    apply ContinuousOn.div_const
    apply ContinuousOn.div_const
    exact ContinuousOn.log (continuous_norm.comp (hcontO _)).continuousOn hne
  have hbound : ∀ c : ℂ, 2 < ‖c‖ → ∀ n : ℕ,
      |potentialSeq n c - mandelbrotPotential c| ≤ (1 / 2 : ℝ) ^ n := by
    intro c hc n
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
    have hdistG : ∀ z : ℂ, escapeRadius c < ‖z‖ → ∀ n : ℕ, dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ 1 / 2 / 2 ^ n := by
      intro z hz n
      have h := hstepG z hz n
      have hw := (hgrowth c z hz n).1
      have hR := hR2 c
      have hwpos : 0 < ‖orbit c z n‖ := by linarith
      have h2w : 2 / ‖orbit c z n‖ ≤ 1 := by
        rw [div_le_one hwpos]
        linarith
      rw [Real.dist_eq]
      unfold logOrbitSeq
      have hp : (0 : ℝ) < 2 ^ n := by positivity
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
    have hlimG : ∀ z : ℂ, escapeRadius c < ‖z‖ →
        Filter.Tendsto (logOrbitSeq c z) Filter.atTop (nhds (escapeRate c z)) := by
      intro z hz
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two (hdistG z hz))
      exact tendsto_nhds_limUnder ⟨l, hl⟩
    have htail : ∀ z : ℂ, escapeRadius c < ‖z‖ → ∀ n : ℕ,
        |logOrbitSeq c z n - escapeRate c z| ≤ (1 / 2 : ℝ) ^ n := by
      intro z hz n
      have h := dist_le_of_le_geometric_two_of_tendsto (C := 1) (hdistG z hz) (hlimG z hz) n
      rw [Real.dist_eq] at h
      have heq : (1 : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]
      rw [heq] at h
      exact h
    have hc2 : 2 < ‖c‖ → escapeRadius c < ‖orbit c 0 2‖ := by
      intro hc
      have hR : escapeRadius c = ‖c‖ := max_eq_right hc.le
      have h2 : orbit c 0 2 = c ^ 2 + c := by
        simp [orbit, MandelbrotEscape.qmap]
      rw [hR, h2]
      have h := norm_sub_le (c ^ 2 + c) c
      simp only [add_sub_cancel_right, norm_pow] at h
      nlinarith
    have h := htail _ (hc2 hc) n
    unfold potentialSeq mandelbrotPotential
    rw [← sub_div, abs_div, abs_two]
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    linarith
  have hunif : TendstoUniformlyOn potentialSeq mandelbrotPotential Filter.atTop {c : ℂ | 2 < ‖c‖} := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn c hc
    rw [dist_comm, Real.dist_eq]
    calc |potentialSeq n c - mandelbrotPotential c| ≤ (1 / 2 : ℝ) ^ n := hbound c hc n
      _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ < ε := hN
  exact hunif.continuousOn (Filter.Eventually.of_forall hcont).frequently
