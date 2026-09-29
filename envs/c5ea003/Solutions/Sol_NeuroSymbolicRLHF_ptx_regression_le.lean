-- Prove2me | solution 1 for NeuroSymbolicRLHF.ptx_regression_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:49:25.014985+00:00
-- url     : https://prove2.me/submissions/5e1f450f-01a3-49e8-b67f-5aa17c5dae83

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    {ref r pre : ι → ℝ}
    (href : IsPosProb ref) (hpre : IsProb pre) :
    ptxTerm γ pre ref - ptxTerm γ pre (gibbs β ref r) ≤ γ * oscil r / β := by
  have hpos := href.pos
  have hZ : 0 < tiltZ β ref r :=
    Finset.sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) Finset.univ_nonempty
  -- `log ref - log π = log Z - r/β`
  have hlog : ∀ i, Real.log (ref i) - Real.log (gibbs β ref r i)
      = Real.log (tiltZ β ref r) - r i / β := by
    intro i
    have hg : gibbs β ref r i = ref i * Real.exp (r i / β) / tiltZ β ref r := rfl
    rw [hg, Real.log_div (mul_pos (hpos i) (Real.exp_pos _)).ne' hZ.ne',
      Real.log_mul (hpos i).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  -- `log Z ≤ max r / β` and `r ≥ min r`
  have hle : ∀ i, r i ≤ univ.sup' univ_nonempty r := fun i => le_sup' r (mem_univ i)
  have hge : ∀ i, univ.inf' univ_nonempty r ≤ r i := fun i => inf'_le r (mem_univ i)
  have hlogZ : Real.log (tiltZ β ref r) ≤ univ.sup' univ_nonempty r / β := by
    rw [Real.log_le_iff_le_exp hZ]
    calc tiltZ β ref r ≤ ∑ i, ref i * Real.exp (univ.sup' univ_nonempty r / β) :=
          sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hle i) hβ.le)) (hpos i).le)
      _ = Real.exp (univ.sup' univ_nonempty r / β) := by rw [← sum_mul, href.sum_one, one_mul]
  have hterm : ∀ i, Real.log (tiltZ β ref r) - r i / β ≤ oscil r / β := by
    intro i
    unfold oscil
    rw [sub_div]
    have := div_le_div_of_nonneg_right (hge i) hβ.le
    linarith
  unfold ptxTerm
  rw [← mul_sub, ← sum_sub_distrib]
  simp only [← mul_sub, hlog]
  have hsum : ∑ i, pre i * (Real.log (tiltZ β ref r) - r i / β) ≤ oscil r / β := by
    calc ∑ i, pre i * (Real.log (tiltZ β ref r) - r i / β) ≤ ∑ i, pre i * (oscil r / β) :=
          sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hpre.nonneg i))
      _ = oscil r / β := by rw [← sum_mul, hpre.sum_one, one_mul]
  calc γ * ∑ i, pre i * (Real.log (tiltZ β ref r) - r i / β) ≤ γ * (oscil r / β) :=
        mul_le_mul_of_nonneg_left hsum hγ
    _ = γ * oscil r / β := by ring
