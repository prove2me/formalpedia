-- Prove2me | solution 1 for mme_integer_regional_step_N2_level_bound
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T20:04:23.639381+00:00
-- url     : https://prove2.me/submissions/c32d5b97-3b5c-4e90-92bf-a19b36b74555

import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : forall (lower : Nat)
    (S : MME.RegionRealization.IntegerStep lower 2 (fun _ _ => True)),
    lower < 3 := by
  intro lower S
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
