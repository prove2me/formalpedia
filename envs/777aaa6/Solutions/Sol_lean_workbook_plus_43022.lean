-- Prove2me | solution 1 for lean_workbook_plus_43022
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:18:57.820475+00:00
-- url     : https://prove2.me/submissions/a2f4e037-b421-49ee-9659-4b85ff8c9482

import Mathlib

set_option autoImplicit false

namespace QuinticRootSixthPowerFloor

def polynomial (x : ℝ) : ℝ := x ^ 5 - x ^ 3 + x - 2

theorem derivative (x : ℝ) :
    HasDerivAt polynomial (5 * x ^ 4 - 3 * x ^ 2 + 1) x := by
  convert ((((hasDerivAt_id x).pow 5).sub ((hasDerivAt_id x).pow 3)).add
    (hasDerivAt_id x)).sub_const 2 using 1
  simp

theorem derivative_positive (x : ℝ) : 0 < 5 * x ^ 4 - 3 * x ^ 2 + 1 := by
  have h : 20 * (5 * x ^ 4 - 3 * x ^ 2 + 1) = (10 * x ^ 2 - 3) ^ 2 + 11 := by
    ring
  nlinarith [sq_nonneg (10 * x ^ 2 - 3)]

theorem strictly_increasing : StrictMono polynomial :=
  strictMono_of_hasDerivAt_pos derivative derivative_positive

theorem endpoint_signs : polynomial (1201 / 1000) < 0 ∧ 0 < polynomial (5 / 4) := by
  norm_num [polynomial]

theorem exists_zero : ∃ a : ℝ, polynomial a = 0 := by
  have hc : Continuous polynomial := by unfold polynomial; fun_prop
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc
    (by norm_num : (1201 / 1000 : ℝ) ≤ 5 / 4) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (polynomial (1201 / 1000)) (polynomial (5 / 4)) from
      ⟨le_of_lt endpoint_signs.1, le_of_lt endpoint_signs.2⟩)
  exact ⟨a, ha⟩

theorem unique_zero : ∃! a : ℝ, polynomial a = 0 := by
  obtain ⟨a, ha⟩ := exists_zero
  exact ⟨a, ha, fun b hb => strictly_increasing.injective (hb.trans ha.symm)⟩

noncomputable def root : ℝ := Classical.choose exists_zero

theorem root_equation : polynomial root = 0 := Classical.choose_spec exists_zero

theorem classification (a : ℝ) : polynomial a = 0 ↔ a = root := by
  constructor
  · intro ha
    exact strictly_increasing.injective (ha.trans root_equation.symm)
  · rintro rfl
    exact root_equation

theorem root_bounds (a : ℝ) (ha : polynomial a = 0) :
    1201 / 1000 < a ∧ a < 5 / 4 := by
  constructor
  · apply strictly_increasing.lt_iff_lt.mp
    rw [ha]
    exact endpoint_signs.1
  · apply strictly_increasing.lt_iff_lt.mp
    rw [ha]
    exact endpoint_signs.2

theorem sixth_power_bounds (a : ℝ) (ha : polynomial a = 0) :
    3 < a ^ 6 ∧ a ^ 6 < 4 := by
  obtain ⟨hl, hu⟩ := root_bounds a ha
  have hpos : 0 ≤ a := by linarith
  have hp : (1201 / 1000 : ℝ) ^ 6 < a ^ 6 :=
    pow_lt_pow_left₀ hl (by norm_num) (by norm_num)
  have hq : a ^ 6 < (5 / 4 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ hu hpos (by norm_num)
  constructor <;> norm_num at * <;> linarith

theorem source_floor (a : ℝ) (ha : polynomial a = 0) : ⌊a ^ 6⌋ = 3 := by
  obtain ⟨hl, hu⟩ := sixth_power_bounds a ha
  apply Int.floor_eq_iff.mpr
  norm_num
  exact ⟨hl.le, hu⟩

theorem source_nonvacuous :
    ∃ a : ℝ, a ^ 5 - a ^ 3 + a - 2 = 0 ∧ 3 < a ^ 6 ∧ a ^ 6 < 4 ∧ ⌊a ^ 6⌋ = 3 := by
  obtain ⟨a, ha⟩ := exists_zero
  exact ⟨a, ha, (sixth_power_bounds a ha).1, (sixth_power_bounds a ha).2, source_floor a ha⟩

end QuinticRootSixthPowerFloor

theorem solution (a : ℝ) (ha : a ^ 5 - a ^ 3 + a - 2 = 0) : ⌊a ^ 6⌋ = 3 :=
  QuinticRootSixthPowerFloor.source_floor a ha
