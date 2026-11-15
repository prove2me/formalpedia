-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:07.118642+00:00
-- url     : https://prove2.me/theorems/8a084ef5-4546-41a5-8299-6d8e9a2cb34d
-- title:
--   A finite search budget for ordered preliminary regularity
-- statement:
--   For natural parameters $k,j$ and a real tolerance $\tau$, the regularity budget is
--
--   $$
--   \left\lceil\frac{|\operatorname{OrderedFace}(k,j+1)|}{\tau^2}\right\rceil_{\mathbb N}+1.
--   $$
--
--   The natural ceiling and the extra one produce a total natural-valued expression. For positive tolerances, the later energy argument uses this as a sufficiently long preliminary-regularity search. Positivity of the tolerance is an application hypothesis, not part of the definition.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalParameters.lean#L304-L311

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
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
# Quantitative parameters for ordered hypergraph removal

This file contains only the numerical layer of ordered removal.  Semantic
cover and contradiction arguments live elsewhere.

For a removal allowance `ξ > 0` and a uniform bound `M` on every selected
fine partition, write `S` for the number of positive subfaces of one top
face and `N` for the number of positive faces in the whole ordered
configuration.  We choose

```
ρ = min (1 / 2) (ξ / (4 * (S * M + 1))),
θ = ρ ^ N / (4 * (N + 1)),
α = ρ,   δ = η = θ,   β = θ²,
γ = ξ * β / 4.
```

Then the sharp cleaning error is at most

```
S * M * α + γ / β ≤ ξ / 2 < ξ,
```

whereas the configuration-count lower bound is strictly positive because

```
N * (η + δ) < ρ ^ N.
```

The final sections give ambient-independent ceiling schedules for weak
regularity and frozen-upper energy selection, derive a uniform complexity
bound from `StrongOrderedComplexRegularityCertificate`, and state bridge
theorems.  The bridge makes the remaining diagonal compatibility
transparent: the selected regularity tolerance must be at most `θ`, and
the reciprocal-timescale energy budget must be at most `γ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Face counts and explicit thresholds -/











































/-! ## Arithmetic margins -/











/-! ## Ambient-independent ceiling schedules -/

/-- A ceiling budget which is long enough to run one preliminary
regularity pass at tolerance `τ`. -/
noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1



















/-! ## A uniform complexity bound for the strong certificate -/







namespace StrongOrderedComplexRegularityCertificate



end StrongOrderedComplexRegularityCertificate

/-! ## Rank-sensitive target interface

The current counting theorem replaces every density floor by one global
`ρ` and every analytic error by global maxima `η, δ`.  The following
formulas record the sharper rank-dependent target without asserting a new
counting theorem.

* `orderedRemovalRankCleaningError` is the exact rankwise analogue of the
  sharp deletion estimate: upper complexity times `α`, plus the rank gap
  divided by `β`.
* `orderedRemovalRankDensityProduct` is the product of the actual
  rank-dependent density floors over all positive faces.
* `orderedRemovalRankCountingError` is one rank-dependent analytic error
  per positive face.

A rank-sensitive recurrence proving `count ≥ densityProduct - countingError`
would remove the present `min α` / `max ε` collapse.  Whether that interface,
together with a diagonal strong selector, closes the remaining schedule
feedback is deliberately left as a separate mathematical obligation.
-/









/-! ## Bridge from a compatible strong certificate -/



namespace StrongOrderedComplexRegularityCertificate







end StrongOrderedComplexRegularityCertificate

end Wikipedia.SzemeredisTheorem


