-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_realSmoothExponentShell_bounds
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:42:51.295979+00:00
-- url     : https://prove2.me/theorems/abef78b2-4255-4e8d-93e5-eb5dc7476ecf
-- title:
--   RealSmoothExponentShell bounds
-- statement:
--   Let p,q,r and hp,hq,hr be natural numbers, with p>0 and r>0, and let lo,hi be real. The smooth-exponent shell in [lo,hi) has at most (hp+1)(hq+1) points if hi≤r·lo, and at most (hq+1)(hr+1) if hi≤p·lo. If hi≤r·lo, hp≤hq≤hr and hp+hq+hr=j, then nine times its cardinality is at most (j+3)^2.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L283-L306
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
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealCutoffs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.ModEq
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

namespace PaperR10
end PaperR10

/-!
# Literal real cutoffs for the Erdős 269 paper

The paper quantifies its prefix cutoffs and shell endpoints over the reals.
This module transports the existing natural-cutoff arithmetic through
`Nat.floor` and proves the short-shell injection directly for real endpoints.
-/


open Finset
open scoped BigOperators

noncomputable section

open PaperR10

open ErdosProblems.Erdos269.PaperCompleteR20

open ErdosProblems.Erdos269.PaperR10

theorem ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds
    {p q r hp hq hr j : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ (r : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hp + 1) * (hq + 1)) ∧
    (hi ≤ (p : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hq + 1) * (hr + 1)) ∧
    (hi ≤ (r : ℝ) * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (j + 3) ^ 2) := by sorry
