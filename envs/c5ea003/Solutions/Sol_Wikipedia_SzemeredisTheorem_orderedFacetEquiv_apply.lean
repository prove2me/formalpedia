-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.orderedFacetEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:06.644195+00:00
-- url     : https://prove2.me/submissions/12ee05f9-df14-4ef0-ab39-8d26d0cf8c19

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
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
@[simp]
theorem solution
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp
