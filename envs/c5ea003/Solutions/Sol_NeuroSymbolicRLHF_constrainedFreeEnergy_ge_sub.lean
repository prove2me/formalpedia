-- Prove2me | solution 1 for NeuroSymbolicRLHF.constrainedFreeEnergy_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:53:45.138171+00:00
-- url     : https://prove2.me/submissions/fc82ca0d-6a09-4405-8b03-44428fd8e9b7

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Definitions.Def_Speculative_AutoResearch_RLHFSymbolicConstraintLattice
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 < β) [Nonempty ι]
    {ref r : ι → ℝ}
    {S : Finset ι} (href : IsPosProb ref) (hS : S.Nonempty) :
    freeEnergy β ref r - constrainedFreeEnergy β ref r S
      ≤ oscil r - β * Real.log (∑ i ∈ S, ref i) := by
  have hpos := href.pos
  have hle : ∀ i, r i ≤ univ.sup' univ_nonempty r := fun i => le_sup' r (mem_univ i)
  have hge : ∀ i, univ.inf' univ_nonempty r ≤ r i := fun i => inf'_le r (mem_univ i)
  have hZ : 0 < tiltZ β ref r :=
    sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) univ_nonempty
  have hSref : 0 < ∑ i ∈ S, ref i := sum_pos (fun i _ => hpos i) hS
  -- `log Z ≤ max r / β`
  have hlogZ : Real.log (tiltZ β ref r) ≤ univ.sup' univ_nonempty r / β := by
    rw [Real.log_le_iff_le_exp hZ]
    calc tiltZ β ref r ≤ ∑ i, ref i * Real.exp (univ.sup' univ_nonempty r / β) :=
          sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hle i) hβ.le)) (hpos i).le)
      _ = Real.exp (univ.sup' univ_nonempty r / β) := by rw [← sum_mul, href.sum_one, one_mul]
  -- `Z_S ≥ (Σ_S ref) e^{min r / β}`
  have hZS : (∑ i ∈ S, ref i) * Real.exp (univ.inf' univ_nonempty r / β) ≤ constrainedZ β ref r S := by
    unfold constrainedZ
    rw [sum_mul]
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hge i) hβ.le)) (hpos i).le)
  have hlogZS : Real.log (∑ i ∈ S, ref i) + univ.inf' univ_nonempty r / β
      ≤ Real.log (constrainedZ β ref r S) := by
    have h := Real.log_le_log (mul_pos hSref (Real.exp_pos _)) hZS
    rwa [Real.log_mul hSref.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  unfold freeEnergy constrainedFreeEnergy oscil
  have h1 := mul_le_mul_of_nonneg_left hlogZ hβ.le
  have h2 := mul_le_mul_of_nonneg_left hlogZS hβ.le
  rw [mul_div_cancel₀ _ hβ.ne'] at h1
  rw [mul_add, mul_div_cancel₀ _ hβ.ne'] at h2
  linarith
