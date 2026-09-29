-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_carryMajorantQtilde_lt_Q
-- name    : ErdosProblems.Erdos269.carryMajorantQtilde_lt_Q
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:36:59.029682+00:00
-- url     : https://prove2.me/theorems/91456fa4-b328-48ea-9f3a-92cbd25c3d33
-- title:
--   CarryMajorantQtilde lt Q
-- statement:
--   The sharp rational carry majorant is strictly smaller than the original at every natural rank.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/JumpConstraintMajorant.lean#L119-L128
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_JumpConstraintMajorant
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

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.carryMajorantQtilde_lt_Q (n : ℕ) :
    carryMajorantQtilde n < carryMajorantQ n := by sorry
