-- Prove2me | solution 1 for ErdosProblems.Erdos269.carryMajorantQ_sub_Qtilde
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:35:33.908732+00:00
-- url     : https://prove2.me/submissions/35ac8f8e-daa1-4c57-bff7-ddf0c94d5eb3

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

open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution (n : ℕ) :
    carryMajorantQ n - carryMajorantQtilde n =
      (121 * (n : ℚ) ^ 2 + 1518 * n + 5111) / 11979 := by
  unfold carryMajorantQ carryMajorantQtilde
  field_simp
  ring
