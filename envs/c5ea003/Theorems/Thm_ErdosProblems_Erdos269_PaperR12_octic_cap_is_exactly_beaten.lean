-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR12_octic_cap_is_exactly_beaten
-- name    : ErdosProblems.Erdos269.PaperR12.octic_cap_is_exactly_beaten
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:06:27.352007+00:00
-- url     : https://prove2.me/theorems/08ce6e4b-75ab-467c-854e-91c6598259a0
-- title:
--   Octic cap is exactly beaten
-- statement:
--   A cap G satisfying G(B,n)/8^n→0 is eventually beaten, together with the quadratic state width, by the actual window modulus.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/R12/OcticWindowBand.lean#L19-L72
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

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
import Definitions.Def_ErdosProblems_Erdos269_PaperR8RankMajorant
import Definitions.Def_ErdosProblems_Erdos269_ActualSharpTailMajorantR10
import Definitions.Def_ErdosProblems_Erdos269_SharpWindowCapR10
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
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace ErdosProblems.Erdos269.PaperR12
end ErdosProblems.Erdos269.PaperR12

namespace PaperR10
end PaperR10

namespace PaperR11
end PaperR11

namespace PaperR7
end PaperR7

namespace PaperR8
end PaperR8

/-!
# Enlarged equivalence band: little-o(8^a), rather than little-o(2^a)

For the actual 2,3,5 height word, 8^len/15 < W. Keeping this exact scale
strictly enlarges the sufficient decay condition in the long paper. The
carry-dominating lower bound is still required. No irrationality producer
is assumed or proved unconditionally. A source-current public Wave A audit checked
the named declarations with only the permitted axioms; see
`verification/erdos269-wavea-validation.json`. A later comment-only edit requires
the same focused audit to refresh its byte-level source binding.
-/
open PaperR7 PaperR8 PaperR10 PaperR11 Filter
open scoped Topology

open ErdosProblems.Erdos269.PaperR12

open ErdosProblems.Erdos269.PaperR10
open ErdosProblems.Erdos269.PaperR7
open ErdosProblems.Erdos269.PaperR8

theorem ErdosProblems.Erdos269.PaperR12.octic_cap_is_exactly_beaten (G : ℕ → ℕ → ℕ)
    (hsmall : ∀ B, 0 < B →
      Tendsto (fun n : ℕ => (G B n : ℝ) / (8 : ℝ) ^ n) atTop (𝓝 0)) :
    ∀ B lo : ℕ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ len : ℕ, 0 < len ∧
        ((max (G B (lo + len)) (B * bridgeWidth (lo + len)) : ℕ) : ℝ) /
          (actualWindowBase lo len : ℝ) < ε := by sorry
