-- Prove2me | solution 1 for TraceBattery.Hb_le_logb_card_img
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T14:30:32.663015+00:00
-- url     : https://prove2.me/submissions/b909e8af-eb27-4603-a55d-28d997ab4e6d

import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
open TraceBattery in
theorem solution {Ω : Type*} [Fintype Ω] {α : Type*} [Nonempty Ω] (f : Ω → α) :
    Hb f ≤ Real.logb 2 ((img f).card : ℝ) := by
  have hH : H f ≤ Real.log ((img f).card : ℝ) := by
    classical
    have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
    have hpos : ∀ a ∈ img f, (0 : ℝ) < cnt f a := by
      intro a ha
      unfold img at ha
      rw [Finset.mem_image] at ha
      obtain ⟨x, _, rfl⟩ := ha
      unfold cnt fib
      exact_mod_cast Finset.card_pos.mpr ⟨x, by simp⟩
    have hsum : ∑ a ∈ img f, (cnt f a : ℝ) = Fintype.card Ω := by
      unfold cnt fib img
      rw [← Nat.cast_sum]
      congr 1
      rw [← Finset.card_univ]
      exact (Finset.card_eq_sum_card_image f Finset.univ).symm
    have hw : ∑ a ∈ img f, (cnt f a : ℝ) / Fintype.card Ω = 1 := by
      rw [← Finset.sum_div, hsum, div_self hN.ne']
    have hj := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := img f)
      (w := fun a => (cnt f a : ℝ) / Fintype.card Ω) (p := fun a => (Fintype.card Ω : ℝ) / cnt f a)
      (fun a _ => div_nonneg (Nat.cast_nonneg _) hN.le) hw (fun a ha => div_pos hN (hpos a ha))
    simp only [smul_eq_mul] at hj
    have hsimp : ∑ a ∈ img f, (cnt f a : ℝ) / Fintype.card Ω * ((Fintype.card Ω : ℝ) / cnt f a)
        = (img f).card := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have h1 := (hpos a ha).ne'
      field_simp
      simp
    rw [hsimp] at hj
    exact hj
  unfold Hb
  rw [Real.logb]
  exact div_le_div_of_nonneg_right hH (Real.log_pos (by norm_num)).le
