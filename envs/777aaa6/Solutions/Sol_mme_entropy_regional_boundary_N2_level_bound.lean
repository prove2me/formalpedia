-- Prove2me | solution 1 for mme_entropy_regional_boundary_N2_level_bound
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T20:03:56.629873+00:00
-- url     : https://prove2.me/submissions/e9917045-ebd9-4186-bf79-7960706e85d6

import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : forall (lower : Nat) (P : MME.ProfiledCW.Predicate 2)
    (B : MME.ProfiledCW.BoundaryEnd lower 2 P),
    lower < 3 := by
  intro lower P B
  by_contra h
  push_neg at h
  have h2 : 2 ≤ lower - 1 := by omega
  have h4 : 4 ≤ 2 ^ (lower - 1) := by
    calc (4 : Nat) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (lower - 1) := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
  have hlen := B.length
  cases heq : B.L with
  | zero =>
    rw [heq] at hlen
    simp at hlen
  | succ n =>
    have hge : 1 * 4 ≤ B.L * 2 ^ (lower - 1) :=
      Nat.mul_le_mul (by omega) h4
    omega
