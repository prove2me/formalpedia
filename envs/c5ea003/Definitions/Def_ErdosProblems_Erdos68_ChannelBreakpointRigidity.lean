-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_ChannelBreakpointRigidity
-- name    : ErdosProblems_Erdos68_ChannelBreakpointRigidity
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T00:51:14.561355+00:00
-- url     : https://prove2.me/theorems/a0c36cb6-a876-42e9-a862-192c6f88a966
-- title:
--   Finite factorial moments and divisor-channel numerators
-- statement:
--   Defines, for a finite integer coefficient family and natural-number index family, the integer factorial-weighted sum and the integer numerator of a divisor channel d using natural-number division by (d!)^(index/d). These definitions make no cancellation or irrationality claim.
-- source:
--   Pinned Lean definitions factorialMoment and channelNumerator: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/ChannelBreakpointRigidity.lean#L23-L30; the source module states their finite-family namespace is distinct from the Finsupp presentation, with no novelty or whole-problem claim.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Channel breakpoint rigidity for Erdős problem 68

For a finite coefficient family whose indices all lie in one quotient band
`[k d, (k + 1) d)`, every factorial coefficient is the same fixed multiple
`(d!)^k` of its `d`-channel coefficient.  Hence cancellation of that channel
forces cancellation of the factorial moment.  In the first band, a nonzero
factorial moment together with channel cancellation requires at least one
support index to reach the breakpoint `2d`.

The namespace `Erdos68` is the finite-family presentation; it is distinct
from the Finsupp presentation in `ErdosProblems.Erdos68`.  No declaration
constructs a cancelling coefficient family, treats several channels
simultaneously, estimates a residual, or decides rationality of the #68
series.
-/

namespace Erdos68

/-- Factorial-weighted sum of a finite coefficient family. -/
def factorialMoment {ι : Type*} [Fintype ι] (coeff : ι → ℤ) (index : ι → ℕ) : ℤ :=
  ∑ j, coeff j * (index j).factorial

/-- The integer numerator of the `d`-th divisor channel. -/
def channelNumerator {ι : Type*} [Fintype ι]
    (coeff : ι → ℤ) (index : ι → ℕ) (d : ℕ) : ℤ :=
  ∑ j, coeff j * ((index j).factorial / d.factorial ^ (index j / d) : ℕ)

















end Erdos68


