-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:10:11.083988+00:00
-- url     : https://prove2.me/theorems/c51d0e30-b6d3-42e5-9d2f-85ff5f2765d9
-- title:
--   A choice-free maximum of a finite natural family
-- statement:
--   For a family of natural numbers indexed by $\operatorname{Fin}(n)$, the finite maximum is defined recursively. The empty family has value zero. At successor size, the value is the maximum of the previous family's value and the final coordinate.
--
--   This computes a bound without choosing an index at which it is attained. It provides the finite maximum used to combine rankwise complexity estimates in the later growth-function construction.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/TowerDominatingGrowth.lean#L303-L311

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
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
# Finite-stage tower-dominating growth functions

The triangular regularity schedule at rank `j` has one-step map

```
T_{F,j}(M) =
  (2^(j+1))^(orderedRemovalRegularityBudget k j (1 / F(M))) * M.
```

It is circular to ask, without further proof, for one growth function to
dominate the tower map formed from its own reciprocal tolerance.  The finite
regularity argument does not need such a fixed point.  Instead, this file
constructs a sequence

```
F₀ = F,   F_{s+1} = majorant of F_s and every T_{F_s,j}, j < r.
```

The construction first takes bounded maxima in the complexity variable and
then a finite maximum over the relevant ranks.  Consequently every `F_s` is
monotone and strictly above the diagonal, while `F_{s+1}` dominates every
one-step map computed with `F_s`.  This gives the exact stage-shifted
inequality

```
M_{F_s,j}(n+1) ≤ F_{s+1}(M_{F_s,j}(n)).
```

The last section applies this inequality to every selected rank of
`GrowthFunctionOrderedComplexRegularityCertificate` and embeds each selected
coarse/fine pair in an honest one-step `DescendingGrowthHierarchy`.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The one-step map and bounded envelopes -/

















/-! ## One majorant stage -/











/-! ## Iterated finite-stage closure -/

















/-! ## Finite maxima for simultaneous hierarchy bounds -/

/-- Maximum of a finite family of natural numbers.  The recursive
`Fin.lastCases` presentation is convenient for later all-layer bounds and
does not introduce a choice of an optimizing index. -/
def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))



/-! ## Bridge to selected all-rank certificates -/

namespace GrowthFunctionOrderedComplexRegularityCertificate















/-! ### One hierarchy containing all independently selected layers -/











end GrowthFunctionOrderedComplexRegularityCertificate

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.finiteMaximum.eq_1,
    `Wikipedia.SzemeredisTheorem.finiteMaximum.eq_2,
    `Wikipedia.SzemeredisTheorem.finiteMaximum.eq_def,
    `Wikipedia.SzemeredisTheorem.finiteMaximum.match_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


