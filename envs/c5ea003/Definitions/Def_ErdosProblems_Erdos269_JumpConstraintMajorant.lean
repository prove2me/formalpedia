-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
-- name    : ErdosProblems_Erdos269_JumpConstraintMajorant
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:12:01.141525+00:00
-- url     : https://prove2.me/theorems/dffed80e-5ca1-4ab5-9212-7bfe37b457e2
-- title:
--   JumpConstraintMajorant
-- statement:
--   Defines the original quadratic rational carry majorant Q, the sharper jump-constrained majorant Q-tilde, and exact rational geometric moments used to evaluate them.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/JumpConstraintMajorant.lean#L1-L130
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Erdős #269: the three-consecutive-2-jump obstruction and the Q̃ algebra

The merged ordered list of positive `{2,3,5}`-powers cannot contain three
consecutive powers of two: between `2^e` and `2^{e+2}` there is always a
power of three.  That unique-factorisation fact is the only new arithmetic
input in the improved carry majorant

    Q̃(n) = (1210 n² + 9130 n + 18847) / 11979

relative to the geometric majorant `Q(n) = (n² + 8n + 18)/9` obtained by
using only `multiplier ≥ 2`.  The rational identities below check the
generating-function moments of the constrained weights and the comparison
`Q − Q̃ > 0`.  They do not by themselves bound the actual tail `X_a`; that
assembly is an ordinary proof in the note, using the checked shell
multiplicity bound.  Neither majorant weakens the window-escape producer,
which is already equivalent to irrationality on the whole quadratic family.

Nothing here proves irrationality of the `{2,3,5}` series.
-/

namespace ErdosProblems.Erdos269





/-- Geometric (unconstrained) quadratic majorant. -/
def carryMajorantQ (n : ℕ) : ℚ :=
  ((n : ℚ) ^ 2 + 8 * n + 18) / 9

/-- Jump-constrained quadratic majorant. -/
def carryMajorantQtilde (n : ℕ) : ℚ :=
  (1210 * (n : ℚ) ^ 2 + 9130 * n + 18847) / 11979

















end ErdosProblems.Erdos269


