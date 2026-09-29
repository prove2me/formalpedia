-- Prove2me | solution 1 for EscapeCriterion.critOrbit_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:55:28.054029+00:00
-- url     : https://prove2.me/submissions/7afe111f-341a-4298-b8c9-46e8c52b52a0

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
open EscapeCriterion MandelbrotEscape in
theorem solution (c : ℂ) :
    (∀ n, ‖critOrbit c n‖ ≤ 2) ∨ Filter.Tendsto (fun n => ‖critOrbit c n‖) Filter.atTop Filter.atTop := by
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
  have hco : ∀ n, critOrbit c n = orbit c 0 n := fun n => rfl
  by_cases hall : ∀ n, ‖critOrbit c n‖ ≤ 2
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨n, hn⟩ := hall
    simp only [hco] at hn ⊢
    apply htend' c 0
    by_cases hc : 2 < ‖c‖
    · refine ⟨2, ?_⟩
      have hR : escapeRadius c = ‖c‖ := max_eq_right hc.le
      have h2 : orbit c 0 2 = c ^ 2 + c := by
        simp [orbit, MandelbrotEscape.qmap]
      rw [hR, h2]
      have h := norm_sub_le (c ^ 2 + c) c
      simp only [add_sub_cancel_right, norm_pow] at h
      nlinarith
    · push Not at hc
      have hR : escapeRadius c = 2 := max_eq_left hc
      exact ⟨n, by rw [hR]; exact hn⟩
