-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:10:59.958221+00:00
-- url     : https://prove2.me/theorems/e0270fa7-5323-4716-941d-bc7cf2acc75c
-- title:
--   Deleting top tuples through source-full bad subfaces
-- statement:
--   Fix an ordered coarse/fine complex and rank-dependent real tolerance functions $\alpha,\beta$. For a top ordered face, a tuple is deleted if one of its positive-rank ordered subfaces lies in the source-full bad-base support attached to its own coarse upper atom, using $\alpha$ and $\beta$ at that subface's arity.
--
--   The deleted finite set is the union of the pullbacks over all positive ordered subfaces. Applying this construction separately to each top face gives the source-full deletion family used in the ordered removal argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullOrderedRemoval.lean#L31-L59

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
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
# Source-full bad-base cleaning and the ordered removal contradiction

The source-full counting argument conditions the usual adjacent-boundary
square defect on the join of every proper lower face.  `SourceFullGoodAtoms`
shows that cleaning the resulting bad bases nevertheless costs only

```
upper complexity * density threshold + adjacent atom-energy gap / defect threshold.
```

This file pulls those bad bases back to top faces, records the corresponding
normalized deletion bounds, and proves the semantic cover contradiction.  A
tuple surviving every top-face deletion induces its canonical coarse closed
configuration; factorization of each positive face through a top face shows
that this configuration avoids every source-full bad base and is therefore
source-full mixed-good.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Pulling source-full bad bases back to top faces -/

/-- Delete a top tuple when one of its positive-rank subfaces lies in the
source-full bad base attached to its own coarse upper atom. -/
noncomputable def sourceFullTopBadBaseDeletion
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ) :
    Finset (Fin r → G) := by
  classical
  exact
    (Finset.univ :
      Finset (OrderedPositiveSubface r)).biUnion fun q =>
      orderedFacePullbackFinset q.2
        (P.sourceFullCoarseOwnAtomBadBaseSupport
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (α (q.1.1 + 1))
          (β (q.1.1 + 1)))

/-- Source-full bad-base deletions, one finite set for every top ordered
face. -/
noncomputable def sourceFullBadBaseDeletionFamily
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (α β : ℕ → ℝ) :
    OrderedPattern.DeletionFamily (G := G) k r :=
  fun e => P.sourceFullTopBadBaseDeletion e α β









end OrderedCoarseFineComplex

/-! ## Surviving tuples are source-full mixed-good -/

namespace ClosedOrderedAtomConfiguration



end ClosedOrderedAtomConfiguration

/-! ## Abstract source-good cover contradiction -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


