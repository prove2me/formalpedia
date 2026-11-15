-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingErrorSchedule
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingErrorSchedule
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:18:11.244206+00:00
-- url     : https://prove2.me/theorems/028477ef-d0a0-467d-8575-9c09453bb960
-- title:
--   A recursive numerical budget for relative counting
-- statement:
--   For an ambient natural parameter $m$ and real errors $c,\eta,\xi$, define a real sequence by
--
--   $$
--   E_0=(m+2)c,
--   \qquad
--   E_{r+1}=c+\sqrt{(1+\xi)\bigl(3\eta+2\sqrt{3\eta}+2E_r+4\xi\bigr)}.
--   $$
--
--   The initial stage accounts for bounded telescoping, while each successor adds a direct cut-discrepancy error and the square-root error from Cauchy–Schwarz. The formula is total for arbitrary real parameters; nonnegativity conditions are supplied when applying the error estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingErrorSchedule.lean#L26-L40

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# An explicit error schedule for relative simplex counting

The active-face induction in `RelativeCountingInduction` asks for a scalar
sequence `error`.  Its successor condition is

```text
(1 + ξ) * (3η + 2√(3η) + 2 error(r) + 4ξ)
  ≤ (error(r + 1) - cutError)².
```

This file chooses equality: the next error is `cutError` plus the square
root of the expression on the left.  Nonnegativity of the three input
errors then proves all numerical hypotheses of the active-face induction.
The last section records that every fixed finite stage tends jointly to
zero with the three input errors.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-- The explicit scalar budget used by relative active-face counting.

Stage zero pays for the bounded telescoping base.  Each successor stage
pays one direct face-cut error and the Cauchy--Schwarz square root generated
by the preceding stage. -/
noncomputable def relativeCountingErrorSchedule
    (m : ℕ) (cutError η ξ : ℝ) : ℕ → ℝ
  | 0 => ((m + 2 : ℕ) : ℝ) * cutError
  | r + 1 =>
      cutError +
        Real.sqrt
          ((1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * relativeCountingErrorSchedule m cutError η ξ r +
              4 * ξ))



















/-! ## Arithmetic-progression specialization -/





/-! ## Joint smallness at every fixed finite stage -/







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.relativeCountingErrorSchedule.match_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


