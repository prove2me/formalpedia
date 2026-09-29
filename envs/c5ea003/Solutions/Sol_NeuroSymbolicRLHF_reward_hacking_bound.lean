-- Prove2me | solution 1 for NeuroSymbolicRLHF.reward_hacking_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:33:38.580905+00:00
-- url     : https://prove2.me/submissions/175f76d4-e88c-4b56-940b-536e86de897a

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
open NeuroSymbolicRLHF in
theorem solution {ι : Type*} [Fintype ι] {β ε : ℝ} (hβ : 0 < β) {ref r rhat : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (hε : ∀ i, |r i - rhat i| ≤ ε) :
    freeEnergy β ref r - 2 * ε ≤ rlhfObj β ref r (gibbs β ref rhat) := by
  have hM := hε
  have hpos := href.pos
  have hZ : ∀ s : ι → ℝ, 0 < tiltZ β ref s := fun s =>
    Finset.sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) Finset.univ_nonempty
  set π := gibbs β ref rhat with hπ
  have hπ0 : ∀ i, 0 ≤ π i := fun i => by
    rw [hπ]
    exact div_nonneg (mul_pos (hpos i) (Real.exp_pos _)).le (hZ rhat).le
  have hπsum : ∑ i, π i = 1 := by
    rw [hπ]
    unfold gibbs
    rw [← Finset.sum_div]
    exact div_self (hZ rhat).ne'
  have hlog : ∀ i, Real.log (π i / ref i) = rhat i / β - Real.log (tiltZ β ref rhat) := by
    intro i
    have hq : π i / ref i = Real.exp (rhat i / β) / tiltZ β ref rhat := by
      rw [hπ]
      unfold gibbs
      have := (hpos i).ne'
      field_simp
    rw [hq, Real.log_div (Real.exp_pos _).ne' (hZ rhat).ne', Real.log_exp]
  -- the Gibbs policy of `r̂` attains the free energy of `r̂`
  have hobj : rlhfObj β ref rhat π = freeEnergy β ref rhat := by
    unfold rlhfObj klDivFin freeEnergy
    simp only [hlog, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπsum, one_mul]
    have hr : ∑ i, π i * (rhat i / β) = (∑ i, π i * rhat i) / β := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hr]
    field_simp
    ring
  -- switching the reward from `r̂` to `r` costs at most `M`
  have hswitch : rlhfObj β ref r π = rlhfObj β ref rhat π + ∑ i, π i * (r i - rhat i) := by
    unfold rlhfObj
    rw [show ∑ i, π i * (r i - rhat i) = ∑ i, π i * r i - ∑ i, π i * rhat i by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)]
    ring
  have hlow : -ε ≤ ∑ i, π i * (r i - rhat i) := by
    calc -ε = ∑ i, π i * (-ε) := by rw [← Finset.sum_mul, hπsum]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hM i)).1]) (hπ0 i))
  -- and `F(r) ≤ F(r̂) + M` since `r ≤ r̂ + M`
  have hup : freeEnergy β ref r ≤ freeEnergy β ref rhat + ε := by
    unfold freeEnergy
    have h1 : tiltZ β ref r ≤ Real.exp (ε / β) * tiltZ β ref rhat := by
      unfold tiltZ
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun i _ => ?_)
      have he : Real.exp (r i / β) ≤ Real.exp (ε / β) * Real.exp (rhat i / β) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hβ.le
        linarith [(abs_le.mp (hM i)).2]
      have := mul_le_mul_of_nonneg_left he (hpos i).le
      linarith
    have h2 := Real.log_le_log (hZ r) h1
    rw [Real.log_mul (Real.exp_pos _).ne' (hZ rhat).ne', Real.log_exp] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
    rw [mul_add, mul_div_cancel₀ _ hβ.ne'] at h3
    linarith
  rw [hswitch, hobj]
  linarith
