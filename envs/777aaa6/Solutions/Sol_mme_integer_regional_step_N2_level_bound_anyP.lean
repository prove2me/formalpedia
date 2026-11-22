-- Prove2me | solution 1 for mme_integer_regional_step_N2_level_bound_anyP
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T14:50:56.379039+00:00
-- url     : https://prove2.me/submissions/2ba9ed7e-2fa6-4566-80b0-08d4a9dd0fa2

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : forall (lower : Nat) (P : MME.ProfiledCW.Predicate 2)
    (S : MME.RegionRealization.IntegerStep lower 2 P),
    lower < 3 := by
  intro lower P S
  by_contra h
  push_neg at h
  have h2 : 2 ≤ lower - 1 := by omega
  have h4 : 4 ≤ 2 ^ (lower - 1) := by
    calc (4 : Nat) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (lower - 1) := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
  have hlen := S.length
  cases heq : S.L with
  | zero =>
    rw [heq] at hlen
    simp at hlen
  | succ n =>
    have hge : 1 * 4 ≤ S.L * 2 ^ (lower - 1) :=
      Nat.mul_le_mul (by omega) h4
    omega
