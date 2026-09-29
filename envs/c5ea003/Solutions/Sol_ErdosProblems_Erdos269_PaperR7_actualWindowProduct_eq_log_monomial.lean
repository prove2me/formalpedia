-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR7.actualWindowProduct_eq_log_monomial
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:04:12.896008+00:00
-- url     : https://prove2.me/submissions/80bd76ce-89f4-40ff-b788-29df9918087b

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_PaperR7ActualOrbit
import Definitions.Def_ErdosProblems_Erdos269_PaperR7SeriesIdentification
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7RationalBridge
import Definitions.Def_ErdosProblems_Erdos269_PaperR7WindowResults
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeightQ235_pos
import Theorems.Thm_ErdosProblems_Erdos269_PaperR7_height_windowProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Round 7: exact window statements at the correct bounds

The short cap is `90 B (a+1)^2`. The long cap is `floor(B Q(n_a))`.
They are separately named. No validity claim about the latter is inferred from
the former. The bounded-length obstruction needs only growth of the long cap,
so it can be proved without assuming the unresolved `X_a <= Q(n_a)` bridge.

No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7
open scoped BigOperators
end ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR7 in
theorem solution (lo len : ℕ) :
    actualWindowProduct lo len =
      2 ^ len *
        3 ^ (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) *
        5 ^ (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) := by
  have hpow : (2 : ℕ) ^ lo ≤ 2 ^ (lo + len) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 := Nat.log_mono_right (b := 3) hpow
  have h5 := Nat.log_mono_right (b := 5) hpow
  have hHpos := threePrimeHeightQ235_pos (2 ^ lo)
  apply mul_left_cancel₀ hHpos.ne'
  rw [← height_windowProduct]
  unfold threePrimeHeight
  simp only [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
  -- Abstract the four integer logarithms so that `pow_add` below can only reach
  -- the leading power of two, never the arguments of the logarithms.
  set L3 := Nat.log 3 (2 ^ (lo + len)) with _hL3
  set L5 := Nat.log 5 (2 ^ (lo + len)) with _hL5
  set M3 := Nat.log 3 (2 ^ lo) with _hM3
  set M5 := Nat.log 5 (2 ^ lo) with _hM5
  have he3 : 3 ^ Nat.log 3 (2 ^ (lo + len)) =
      3 ^ Nat.log 3 (2 ^ lo) *
        3 ^ (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) := by
    rw [← pow_add, show Nat.log 3 (2 ^ lo) +
      (Nat.log 3 (2 ^ (lo + len)) - Nat.log 3 (2 ^ lo)) =
      Nat.log 3 (2 ^ (lo + len)) by omega]
  have he5 : 5 ^ Nat.log 5 (2 ^ (lo + len)) =
      5 ^ Nat.log 5 (2 ^ lo) *
        5 ^ (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) := by
    rw [← pow_add, show Nat.log 5 (2 ^ lo) +
      (Nat.log 5 (2 ^ (lo + len)) - Nat.log 5 (2 ^ lo)) =
      Nat.log 5 (2 ^ (lo + len)) by omega]
  rw [pow_add, he3, he5]
  ring
