-- Prove2me | solution 1 for NeuroSymbolicRLHF.le_exp_hilbertDist_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:08:07.914666+00:00
-- url     : https://prove2.me/submissions/b03ed876-8eab-43e3-8f63-a29a491e8ec6

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {p q : ι → ℝ} (hp : IsPosProb p)
    (hq : IsPosProb q) (i : ι) :
    p i ≤ Real.exp (hilbertDist p q) * q i := by
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
