-- Prove2me | solution 2 for NeuroSymbolicRLHF.tvDist_le_expm1_hilbertDist
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:03:01.594093+00:00
-- url     : https://prove2.me/submissions/97ed2b01-055e-4757-a8ce-4b5926af9cf8

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {p q : ι → ℝ} (hp : IsPosProb p)
    (hq : IsPosProb q) :
    tvDist p q ≤ Real.exp (hilbertDist p q) - 1 := by
  -- pointwise likelihood-ratio bound `p i ≤ e^H q i`
  have key : ∀ i, p i ≤ Real.exp (hilbertDist p q) * q i := by
    intro i
    -- both are probability vectors, so some coordinate has `p j ≤ q j`
    obtain ⟨j, hj⟩ : ∃ j, p j ≤ q j := by
      by_contra h
      push_neg at h
      have := sum_lt_sum_of_nonempty univ_nonempty (fun j _ => h j)
      rw [hp.sum_one, hq.sum_one] at this
      exact lt_irrefl _ this
    -- hence the minimal log-ratio is `≤ 0`, and every log-ratio is at most the oscillation
    have hmin : univ.inf' univ_nonempty (fun k => Real.log (p k / q k)) ≤ 0 :=
      (inf'_le _ (mem_univ j)).trans
        (Real.log_nonpos (div_nonneg (hp.pos j).le (hq.pos j).le)
          (div_le_one_of_le₀ hj (hq.pos j).le))
    have hmax : Real.log (p i / q i) ≤ univ.sup' univ_nonempty (fun k => Real.log (p k / q k)) :=
      le_sup' (fun k => Real.log (p k / q k)) (mem_univ i)
    have hH : Real.log (p i / q i) ≤ hilbertDist p q := by
      unfold hilbertDist oscil
      linarith
    have hratio : p i / q i ≤ Real.exp (hilbertDist p q) := by
      rw [← Real.exp_log (div_pos (hp.pos i) (hq.pos i))]
      exact Real.exp_le_exp.mpr hH
    rwa [div_le_iff₀ (hq.pos i)] at hratio
  -- `H ≥ 0`, so `e^H ≥ 1`
  have hH0 : 0 ≤ hilbertDist p q := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    unfold hilbertDist oscil
    have h1 := inf'_le (fun k => Real.log (p k / q k)) (mem_univ j)
    have h2 := le_sup' (fun k => Real.log (p k / q k)) (mem_univ j)
    linarith
  have he : 1 ≤ Real.exp (hilbertDist p q) := Real.one_le_exp hH0
  -- `|p - q| = 2 (p - q)⁺ - (p - q)` and `(p - q)⁺ ≤ (e^H - 1) q`
  have habs : ∀ i, |p i - q i|
      ≤ 2 * ((Real.exp (hilbertDist p q) - 1) * q i) - (p i - q i) := by
    intro i
    have hqi := hq.pos i
    rcases le_total (p i) (q i) with h | h
    · rw [abs_of_nonpos (by linarith)]
      nlinarith
    · rw [abs_of_nonneg (by linarith)]
      have := key i
      nlinarith
  have hsum := sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) => habs i
  rw [sum_sub_distrib, ← mul_sum, ← mul_sum, sum_sub_distrib, hp.sum_one, hq.sum_one] at hsum
  unfold tvDist
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith
