-- Prove2me | solution 1 for mme_dwz_q5_exact_global_profile_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T21:21:53.188657+00:00
-- url     : https://prove2.me/submissions/3718fc38-14b3-423c-bb8b-195d4869692a

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum

open BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace MME.DWZQ5ExactData

open MME.DWZFourthGlobalWitness

theorem scale_pos : 0 < scale := by decide

theorem component_pos : ∀ c, 0 < component c := by decide

theorem component_sum : ∑ c, component c = scale := by decide

theorem component_div_scale_eq_alpha (c : Fin 45) :
    (component c : ℚ) / scale = alpha c := by
  fin_cases c <;> norm_num [component, scale, alpha]

theorem coarseAddress_grade_sum : ∀ c, ∑ i, (coarseAddress c i).val = 8 := by
  decide

theorem coarseAddress_injective : Function.Injective coarseAddress := by
  decide

theorem component_marginal_count : ∀ (i : Fin 3) (g : Fin 9),
    (∑ c : Fin 45, if coarseAddress c i = g then component c else 0) =
      marginal i g := by
  decide

theorem marginal_sum : ∀ i, ∑ g, marginal i g = scale := by decide

theorem marginalXY_eq (g : Fin 9) : marginal 0 g = marginal 1 g := by rfl

theorem rawProfile_support : ∀ c a, 0 < (rawProfile c).count a →
    a.val ≤ (coarseAddress c 2).val ∧ (coarseAddress c 2).val ≤ a.val + 4 := by
  decide

theorem rawProfile_denominator (c : Fin 45) :
    (rawProfile c).denominator = rawDenominator c := rfl

theorem rawProfile_count (c : Fin 45) (a : Fin 5) :
    (rawProfile c).count a = rawCount c a := rfl

abbrev SupportedCell := {v : Fin 3 → Fin 9 // (∑ i, (v i).val) = 8}

theorem supportedCell_card : Fintype.card SupportedCell = 45 := by decide

def supportedLabel (c : Fin 45) : SupportedCell :=
  ⟨coarseAddress c, coarseAddress_grade_sum c⟩

theorem supportedLabel_bijective : Function.Bijective supportedLabel := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    exact coarseAddress_injective (congrArg Subtype.val h)
  · simp only [Fintype.card_fin, supportedCell_card]

noncomputable def supportedLabelEquiv : Fin 45 ≃ SupportedCell :=
  Equiv.ofBijective supportedLabel supportedLabel_bijective

theorem supportedLabelEquiv_val (c : Fin 45) :
    (supportedLabelEquiv c).val = coarseAddress c := rfl

end MME.DWZQ5ExactData

open MME.DWZQ5ExactData MME.DWZFourthGlobalWitness

theorem solution :
    0 < scale ∧
    (∀ c : Fin 45, 0 < component c) ∧
    (∑ c : Fin 45, component c) = scale ∧
    (∀ c : Fin 45, (component c : ℚ) / scale = alpha c) ∧
    (∀ c : Fin 45, ∑ i : Fin 3, (coarseAddress c i).val = 8) ∧
    Function.Injective coarseAddress ∧
    (∀ (i : Fin 3) (g : Fin 9),
      (∑ c : Fin 45, if coarseAddress c i = g then component c else 0) =
        marginal i g) ∧
    (∀ i : Fin 3, ∑ g : Fin 9, marginal i g = scale) ∧
    (∀ g : Fin 9, marginal 0 g = marginal 1 g) ∧
    (∃ e : Fin 45 ≃ {v : Fin 3 → Fin 9 // (∑ i, (v i).val) = 8},
      ∀ c : Fin 45, (e c).val = coarseAddress c) ∧
    (∀ (c : Fin 45) (a : Fin 5), 0 < (rawProfile c).count a →
      a.val ≤ (coarseAddress c 2).val ∧ (coarseAddress c 2).val ≤ a.val + 4) := by
  exact ⟨scale_pos, component_pos, component_sum, component_div_scale_eq_alpha,
    coarseAddress_grade_sum, coarseAddress_injective, component_marginal_count,
    marginal_sum, marginalXY_eq, ⟨supportedLabelEquiv, supportedLabelEquiv_val⟩,
    rawProfile_support⟩

