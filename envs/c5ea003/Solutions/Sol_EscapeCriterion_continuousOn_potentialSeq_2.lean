-- Prove2me | solution 2 for EscapeCriterion.continuousOn_potentialSeq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:36:38.655602+00:00
-- url     : https://prove2.me/submissions/66ffa9dd-42da-4703-ba1f-5e8822ff6777

import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_FilledJuliaCompact
open EscapeCriterion in
theorem solution (n : ℕ) : ContinuousOn (potentialSeq n) {c : ℂ | 2 < ‖c‖} := by
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
  exact hcont n
