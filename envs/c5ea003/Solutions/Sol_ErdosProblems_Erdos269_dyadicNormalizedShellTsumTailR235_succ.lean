-- Prove2me | solution 1 for ErdosProblems.Erdos269.dyadicNormalizedShellTsumTailR235_succ
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:11:35.384994+00:00
-- url     : https://prove2.me/submissions/06db3a7b-57a9-4e87-962c-a958ff61b81a

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellTsumTailR235_eq_shell_add
import Theorems.Thm_ErdosProblems_Erdos269_dyadicNormalizedTailStateR235_succ
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: summability of the actual dyadic shell masses

The ordered source digit has a deliberately coarse quadratic majorant.  The
key point is structural: in a multiplicative interval of width two, fixing the
`3`- and `5`-exponents determines the `2`-exponent, while both odd exponents
are smaller than the dyadic scale.  This gives at most `(a+1)^2` shell points.
-/

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (a : ℕ) :
    dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) =
      dyadicBlockBase235 a *
          dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a -
        dyadicOrderedBlockDigit235 a :=
  dyadicNormalizedTailStateR235_succ dyadicShellTsumTailR235
    dyadicShellTsumTailR235_eq_shell_add a
