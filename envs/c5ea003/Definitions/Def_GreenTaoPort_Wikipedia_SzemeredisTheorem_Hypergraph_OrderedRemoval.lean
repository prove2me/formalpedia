-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:36.375207+00:00
-- url     : https://prove2.me/theorems/702276f1-8aec-4a20-9c2b-21b34d451da9
-- title:
--   Positive ordered subfaces and pullbacks of deleted sets
-- statement:
--   A positive ordered subface of an $r$-tuple consists of a rank choice $j<r$ and an ordered face of arity $j+1$. Storing one less than the arity ensures that every represented face has positive rank.
--
--   For an ordered face of arity $j$ and a finite set of $j$-tuples, its pullback is the finite set of full $r$-tuples whose restriction to that face lies in the specified set. The definition uses the exact ordered coordinate-restriction map and is used to lift lower-face deletions into the ambient tuple space.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemoval.lean#L264-L325

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
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
# Bad-base cleaning for ordered hypergraph complexes

For each upper tuple, the frozen fine upper partition chooses a unique
genuine atom.  The tuple is bad when its coarse boundary lies in the bad
base attached to that very atom.  Summing over the disjoint upper atoms gives
the sharp
cleaning estimate

```
mass(own-atom bad base) ≤
  complexity(upper) * densityThreshold
    + atomEnergyGap / defectThreshold.
```

The second half of the file pulls these bad sets back to every subface of a
top ordered edge.  Exact finite Fubini preserves normalized density, and a
finite union bound gives the deletion-cost estimate needed by ordered
hypergraph removal.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Finite union bounds -/





/-! ## The bad base attached to the tuple's own upper atom -/









/-! ## Ordered specialization -/







/-! ## Pullback to top faces -/

/-- A positive-rank ordered subface of an `r`-tuple.  The first component
stores one less than its arity. -/
abbrev OrderedPositiveSubface (r : ℕ) :=
  (j : Fin r) ×' OrderedFace r (j.1 + 1)



/-- Pull a finite set on one ordered face back to the full tuple space. -/
noncomputable def orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    Finset (Fin r → G) := by
  classical
  exact Finset.univ.filter fun y =>
    orderedFaceTuple d y ∈ S

















/-! ## Surviving tuples induce good closed configurations -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.orderedFacePullbackFinset.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


