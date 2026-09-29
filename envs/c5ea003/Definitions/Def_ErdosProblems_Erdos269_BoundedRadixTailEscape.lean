-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
-- name    : ErdosProblems_Erdos269_BoundedRadixTailEscape
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:56.723289+00:00
-- url     : https://prove2.me/theorems/0f6b09b4-052f-4105-baef-0d6902b0d4a8
-- title:
--   BoundedRadixTailEscape
-- statement:
--   Defines being within a strict distance δ of some integer and being at least δ from every integer. These predicates describe the near/far alternatives for a real affine orbit.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/BoundedRadixTailEscape.lean#L1-L207
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Tactic

/-!
# Erdős #269: bounded-radix tail escape

Consider an affine orbit
`x (n + 1) = P n * x n - c n` with integral `c n` and radices
`2 ≤ P n ≤ 30`.  If the orbit is eventually always within `1/31` of an
integer, the corresponding errors grow by at least a factor of two at every
step; hence one of the states is itself integral.  Otherwise the orbit is at
least `1/31` from every integer at arbitrarily late indices.

The integral state in the first alternative need not be zero.  The theorem
also makes no assertion that the separated indices are eventually all
indices, have positive density, or have unbounded distance from the integers.
-/

namespace ErdosProblems.Erdos269

/-- A real number lies strictly within `δ` of an integer. -/
def NearInteger (x δ : ℝ) : Prop :=
  ∃ z : ℤ, |x - (z : ℝ)| < δ

/-- A real number is at least `δ` from every integer. -/
def FarFromIntegers (x δ : ℝ) : Prop :=
  ∀ z : ℤ, δ ≤ |x - (z : ℝ)|









end ErdosProblems.Erdos269


