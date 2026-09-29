-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_RealCutoffR10
-- name    : ErdosProblems_Erdos269_RealCutoffR10
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:15:30.876975+00:00
-- url     : https://prove2.me/theorems/19328ade-2c93-4076-b34c-23950f0ca4c5
-- title:
--   RealCutoffR10
-- statement:
--   Defines smooth-prefix exponent sets, their LCM, and the three-prime height at a real cutoff through natural floors of real logarithms.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/RealCutoffR10.lean#L1-L128
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

                                                                               
                                                                                
                                                                         
                                        
namespace ErdosProblems.Erdos269.PaperR10

open scoped BigOperators







noncomputable def realPrefixExponents (p q r : ℕ) (x : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (⌊Real.logb p x⌋₊ + 1)).product
    ((Finset.range (⌊Real.logb q x⌋₊ + 1)).product
      (Finset.range (⌊Real.logb r x⌋₊ + 1)))).filter
        (fun e => (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ≤ x)

noncomputable def realPrefixLcm (p q r : ℕ) (x : ℝ) : ℕ :=
  (realPrefixExponents p q r x).lcm
    (fun e => smooth3Val p q r e.1 e.2.1 e.2.2)

noncomputable def realThreePrimeHeight (p q r : ℕ) (x : ℝ) : ℕ :=
  p ^ ⌊Real.logb p x⌋₊ * q ^ ⌊Real.logb q x⌋₊ * r ^ ⌊Real.logb r x⌋₊









end ErdosProblems.Erdos269.PaperR10


