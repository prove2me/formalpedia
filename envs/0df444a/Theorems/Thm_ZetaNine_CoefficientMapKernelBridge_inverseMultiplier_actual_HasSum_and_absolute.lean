-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute
-- name    : ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T10:49:05.9231+00:00
-- url     : https://prove2.me/theorems/bbc02826-16b1-4012-ac43-0462f90498df
-- title:
--   The actual inverse multiplier has its prescribed sum and absolute convergence
-- statement:
--   For each even n>=2 and b:Fin5->Rat, the actual inverse rational quartic multiplier produces a HasSum of the actual weightedR at positive integers with value prescribedL(b), and its absolute norms are Summable. The input b contains the rational constant and zeta3,5,7,9 coefficients. This is the original genuine HasSum, not a totalized tsum identity. Integer inverse coefficients, height bounds and irrationality remain unproved here.
-- source:
--   Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb. The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs. Original declaration lines 291–302.

import Definitions.Def_ZetaNine_CoefficientMapKernelBridge

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)) (prescribedL b) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖):= by sorry
