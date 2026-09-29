-- Prove2me | solution 2 for EscapeCriterion.tendsto_atTop_of_exists_escape
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:06:04.382421+00:00
-- url     : https://prove2.me/submissions/836c6a1f-9763-4c08-8214-40f30edb2c20

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
open EscapeCriterion in
theorem solution (c z : ℂ) (h : ∃ N, escapeRadius c < ‖orbit c z N‖) :
    Filter.Tendsto (fun n => ‖orbit c z n‖) Filter.atTop Filter.atTop := by
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
  exact htend' c z h
