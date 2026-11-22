-- Prove2me | solution 1 for mme_entropy_regional_largeN_numerical_package
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-22T21:42:51.269267+00:00
-- url     : https://prove2.me/submissions/9d1cf594-b5fa-4152-8d52-757c23928842
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_numerical_package_step_boundary_four
import Theorems.Thm_mme_surplus_arith_four

set_option autoImplicit false

theorem solution : exists (N lower : Nat) (P : MME.ProfiledCW.Predicate N) (S : MME.RegionRealization.IntegerStep lower N P) (B : MME.ProfiledCW.BoundaryEnd lower N S.output) (copies : Nat), 3 <= N /\ 0 < copies /\ (((copies * 8 ^ S.repairExponent : Nat) : Real) <= S.entropyLower) /\ (1 <= B.a * B.b * B.c) /\ (((7 ^ N : Nat) : Real) < (copies : Real) * (((B.a * B.b * B.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by
  obtain ⟨lower, P, S, B, copies, hcopies, hroom, habc⟩ := mme_numerical_package_step_boundary_four
  refine ⟨4, lower, P, S, B, copies, by omega, hcopies, hroom, by omega, ?_⟩
  exact mme_surplus_arith_four copies (B.a * B.b * B.c) (by omega) habc
