-- Prove2me | solution 1 for Probability.PortfolioRegret.swap_unbounded_on_irredundant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T07:05:51.340016+00:00
-- url     : https://prove2.me/submissions/95344de4-3067-4a02-9dbd-c62aa1ac6db7

import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioIrredundant
import Definitions.Def_Probability_PortfolioNullDial
import Definitions.Def_Probability_PortfolioRegretCore

open Probability.PortfolioRegret Finset in
theorem solution (M : ℚ) :
    ∃ e : ℚ, 0 < e ∧ e ≤ 1 ∧
      (∀ o, 0 ≤ irredW o) ∧ (∑ o, irredW o = 1) ∧
      IrredundantPortfolio irredW (irredCost e) id ∧
      M * (bestConstant irredW (irredCost e) - dialValue irredW (irredCost e) id) <
        min (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 0)
              (fun o => fiberVal irredW (irredCost e) id o 1))
            (swapMassFun (fun o => fiberVal irredW (irredCost e) id o 1)
              (fun o => fiberVal irredW (irredCost e) id o 0)) := by
  set e : ℚ := 1 / (|M| + 1) with he_def
  have hM1 : 0 < |M| + 1 := by positivity
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 := by
    rw [he_def, div_le_one hM1]
    linarith [abs_nonneg M]
  -- every instance is its own fiber
  have hfv : ∀ o s : Fin 3, fiberVal irredW (irredCost e) id o s = irredCost e o s / 3 := by
    intro o s
    simp [fiberVal, irredW, Finset.filter_eq']
    ring
  have hcost0 : ∀ o s : Fin 3, 0 ≤ irredCost e o s := by
    intro o s
    unfold irredCost
    split_ifs <;> linarith
  -- the static/dial gap lies in `[0, 2e/3]`
  have hBC_le : bestConstant irredW (irredCost e) ≤ 2 * e / 3 := by
    unfold bestConstant
    refine (Finset.inf'_le _ (Finset.mem_univ (2 : Fin 3))).trans (le_of_eq ?_)
    simp [EV, irredW, irredCost, Fin.sum_univ_three]
    ring
  have hBC_ge : 0 ≤ bestConstant irredW (irredCost e) := by
    unfold bestConstant
    refine Finset.le_inf' _ _ fun s _ => ?_
    unfold EV
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (by simp [irredW]) (hcost0 ω s)
  have hDV_le : dialValue irredW (irredCost e) id ≤ 0 := by
    unfold dialValue
    have h1 : ∀ o : Fin 3, univ.inf' univ_nonempty (fiberVal irredW (irredCost e) id o) ≤ 0 := by
      intro o
      refine (Finset.inf'_le _ (Finset.mem_univ o)).trans (le_of_eq ?_)
      rw [hfv]
      fin_cases o <;> simp [irredCost]
    exact (Finset.sum_le_sum fun o _ => h1 o).trans (by simp)
  have hDV_ge : 0 ≤ dialValue irredW (irredCost e) id := by
    unfold dialValue
    exact Finset.sum_nonneg fun o _ => Finset.le_inf' _ _ fun s _ => by
      rw [hfv]
      exact div_nonneg (hcost0 o s) (by norm_num)
  -- both swap masses equal `10/3`
  have hswap1 : swapMassFun (fun o => fiberVal irredW (irredCost e) id o 0)
      (fun o => fiberVal irredW (irredCost e) id o 1) = 10 / 3 := by
    simp only [swapMassFun, hfv, Fin.sum_univ_three]
    simp [irredCost]
    norm_num
  have hswap2 : swapMassFun (fun o => fiberVal irredW (irredCost e) id o 1)
      (fun o => fiberVal irredW (irredCost e) id o 0) = 10 / 3 := by
    simp only [swapMassFun, hfv, Fin.sum_univ_three]
    simp [irredCost]
    norm_num
  refine ⟨e, he0, he1, fun o => by simp [irredW], by simp [irredW],
    ?_, ?_⟩
  · -- irredundancy: member `t` is strictly cheaper on its own fiber `t`
    intro s t hst
    refine ⟨t, ?_⟩
    rw [hfv, hfv]
    have h1 : irredCost e t t = 0 := by
      fin_cases t <;> simp [irredCost]
    have h2 : 0 < irredCost e t s := by
      fin_cases s <;> fin_cases t <;> simp_all [irredCost]
    rw [h1]
    exact div_lt_div_of_pos_right h2 (by norm_num)
  · rw [hswap1, hswap2, min_self]
    set d := bestConstant irredW (irredCost e) - dialValue irredW (irredCost e) id with hd
    have hd0 : 0 ≤ d := by linarith
    have hd1 : d ≤ 2 * e / 3 := by linarith
    have h1 : M * d ≤ |M| * d := mul_le_mul_of_nonneg_right (le_abs_self M) hd0
    have h2 : |M| * d ≤ |M| * (2 * e / 3) := mul_le_mul_of_nonneg_left hd1 (abs_nonneg M)
    have h3 : |M| * e < 1 := by
      rw [he_def, mul_one_div, div_lt_one hM1]
      linarith
    nlinarith
