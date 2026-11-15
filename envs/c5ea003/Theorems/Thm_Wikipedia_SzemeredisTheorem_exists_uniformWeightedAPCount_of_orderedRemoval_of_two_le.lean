-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
-- name    : Wikipedia.SzemeredisTheorem.exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:03:52.239087+00:00
-- url     : https://prove2.me/theorems/44444dcf-6ea8-4a17-b960-c40b3f434f46
-- title:
--   Ordered pattern removal yields a uniform weighted AP-count bound
-- statement:
--   Let $k\ge2$ and assume the uniform ordered-pattern removal property with parameters $k,k-1$. For every density $\delta>0$, there is $c>0$ such that the uniform weighted AP-count property holds in length $k$ at density $\delta$ with count bound $c$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Szemeredi/OrderedRemoval.lean#L62-L80

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Dense Szemerédi consequences of ordered hypergraph removal

The equal-vertex bridge turns ordered rank-`r + 1` removal on `r + 2`
classes into cyclic partite simplex removal.  The standard arithmetic-
progression hypergraph construction then gives uniform dense and weighted
Szemerédi bounds.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
    (k : ℕ) (hk : 2 ≤ k)
    (hordered :
      HasUniformOrderedPatternRemoval k (k - 1))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount k δ c := by sorry
