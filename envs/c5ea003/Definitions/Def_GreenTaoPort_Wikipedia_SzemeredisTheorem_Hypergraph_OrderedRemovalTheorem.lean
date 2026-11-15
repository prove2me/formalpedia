-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:07:01.617255+00:00
-- url     : https://prove2.me/theorems/007f437e-8fe3-49a5-b8e8-a89365b238cf
-- title:
--   Embedding a successor-rank top face among positive faces
-- statement:
--   A top ordered face of arity $n+1$ is regarded as a positive face by recording lower-rank index $n$ and retaining the same ordered face. This canonical embedding identifies the top-rank edge deletions with the positive-face deletion family used in the ordered removal argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemovalTheorem.lean#L26-L31

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
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
# The ordered removal cover contradiction

This file joins the three semantic parts of ordered hypergraph removal.

* The top partition remembers the original edge predicates.
* A tuple surviving every bad-base deletion determines a good closed fine
  atom configuration.
* The configuration counting lemma gives every good configuration a
  uniform lower count.

Every tuple counted by the selected configuration remains an occurrence of
the original pattern, because its selected top atoms are edge-monochromatic.
Thus an occurrence surviving all deletions would force the original pattern
count above the assumed small-count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The selected configuration lies inside the original pattern -/

/-- Regard a top face of successor rank as a positive ordered face. -/
def topPositiveOrderedFace
    {k n : ℕ} (e : OrderedFace k (n + 1)) :
    PositiveOrderedFace k (n + 1) where
  lowerRank := Fin.last n
  face := e











/-! ## The cover contradiction -/





end Wikipedia.SzemeredisTheorem


