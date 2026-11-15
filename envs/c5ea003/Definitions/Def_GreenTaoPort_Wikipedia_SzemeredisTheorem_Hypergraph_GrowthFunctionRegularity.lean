-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:59.649071+00:00
-- url     : https://prove2.me/theorems/c8bd3be9-45fe-4bf6-ac49-71bfbe1859b0
-- title:
--   Natural growth functions and reciprocal regularity tolerances
-- statement:
--   A natural growth function $F$ is monotone and satisfies $F(n)\ge n+1$ for every natural $n$. The structure is callable as a function. In particular its values are positive, including at zero.
--
--   At a displayed complexity $M$, the reciprocal tolerance is $1/F(M)$. For an ordered upper-face rank $j+1$ and a real target $\gamma$, the search length is the natural ceiling of the number of such ordered faces divided by $\gamma$, plus one. Positive target assumptions are supplied when this total expression is used in the energy-increment estimate.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/GrowthFunctionRegularity.lean#L28-L246

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# One-rank growth-function regularity

This file packages the preliminary one-rank selector underlying the
growth-function form of hypergraph regularity.  For a natural-valued growth
function `F`, an initial complexity bound `M₀`, and a fixed upper layer, the
schedule is constructed triangularly:

```
M 0       = M₀,
τ n       = 1 / F (M n),
B n       = ⌈card (OrderedFace k (j + 1)) / (τ n)²⌉ + 1,
M (n + 1) = (2^(j+1))^(B n) * M n.
```

The existing fixed-upper tower then selects adjacent coarse and fine stages.
The fine stage is preliminarily regular with error exactly `τ i`; a
one-rank energy pigeonhole makes the coarse/fine gap at most any prescribed
positive `γ`.  All numerical schedules are ambient-independent.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Natural growth functions -/

/-- A natural growth function is monotone and lies strictly above the
diagonal.  The latter hypothesis ensures that all reciprocal tolerances are
positive, including when the initial complexity bound is zero. -/
structure NatGrowthFunction where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  above_diagonal : ∀ n, n + 1 ≤ toFun n

namespace NatGrowthFunction

instance : CoeFun NatGrowthFunction (fun _ => ℕ → ℕ) :=
  ⟨NatGrowthFunction.toFun⟩







end NatGrowthFunction

/-! ## The triangular numerical schedule -/

/-- Reciprocal growth-function tolerance at a displayed complexity. -/
noncomputable def growthRegularityStepTolerance
    (F : NatGrowthFunction) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)































/-! ## A one-rank energy timescale -/

/-- Ceiling length making the rank-`j` aggregate energy increment at most
the prescribed positive target. -/
noncomputable def growthRegularityLength
    (k j : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card
        (OrderedFace k (j + 1)) : ℝ) / γ) +
    1





/-! ## Growth-function fixed-upper selection -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.NatGrowthFunction.ctorIdx,
    `Wikipedia.SzemeredisTheorem.NatGrowthFunction.mk.inj,
    `Wikipedia.SzemeredisTheorem.NatGrowthFunction.mk.injEq,
    `Wikipedia.SzemeredisTheorem.NatGrowthFunction.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.NatGrowthFunction.noConfusionType
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


