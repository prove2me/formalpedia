-- Prove2me | solution 1 for mme_regional_parent_mixture_cube
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:06.085951+00:00
-- url     : https://prove2.me/submissions/4750c74b-6a40-44ec-9653-e0845f5f0d0d

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib
open BigOperators MME MME.RegionRealization MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem frequency_bounds {C W : Type*} [Fintype W] (mu : C → W → ℕ) (c : C) (w : W) :
    cellFrequency mu c w ∈ Set.Icc 0 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hz : ∑ v, mu c v = 0
    · simp [cellFrequency,hz]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))).mpr
      exact_mod_cast Finset.single_le_sum (f := mu c) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ w)

theorem solution {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hmass : ∀ r, ∑ c, m r c = n r) (mu : Cell half R parent → W → ℕ) :
    ∀ r w, parentMixture htotal n m mu r w ∈ Set.Icc 0 1 := by
  intro r w
  have hp c := frequency_bounds mu (⟨r,c⟩ : Cell half R parent) (w 0)
  have hq c := frequency_bounds mu (⟨r,complement (htotal r) c⟩ : Cell half R parent) (w 1)
  constructor
  · unfold parentMixture
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg (fun c _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp c).1) (hq c).1)
  · unfold parentMixture
    by_cases hn : n r = 0
    · simp [hn]
    · apply (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).mpr
      calc
        _ ≤ ∑ c, (m r c : ℝ) := by
          apply Finset.sum_le_sum
          intro c _
          have hc : (m r c : ℝ) * cellFrequency mu ⟨r,c⟩ (w 0) ≤ m r c :=
            mul_le_of_le_one_right (Nat.cast_nonneg _) (hp c).2
          exact (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) (hp c).1) (hq c).2).trans hc
        _ = _ := by exact_mod_cast hmass r
