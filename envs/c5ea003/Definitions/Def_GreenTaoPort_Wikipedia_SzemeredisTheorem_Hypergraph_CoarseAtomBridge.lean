-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:04:54.570406+00:00
-- url     : https://prove2.me/theorems/149bf6ab-b3f2-464c-ab88-5b3544aecf69
-- title:
--   Energy gaps observed through coarse upper-face atoms
-- statement:
--   For a compatible coarse/fine ordered partition complex, the face-level gap compares two atom energies against the same coarse upper-face partition: one conditioned on the fine lower boundary and one conditioned on the coarse lower boundary. The layer-level gap sums the corresponding energies over all ordered upper faces at that rank.
--
--   Thus the upper target is held coarse in both terms; only the lower conditioning boundary is refined. These real-valued differences are defined for each adjacent rank of the complex, with nonnegativity established by later refinement results.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseAtomBridge.lean#L667-L720

import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
# Passing from fine upper atoms to coarse upper atoms

Strong ordered regularity naturally controls every atom of a fine upper
partition, while the removal argument benefits from choosing its closed
configuration in a fixed coarse complex.  This file supplies the finite
bridge between those two choices.

For a refinement `fineUpper ≤ coarseUpper`, every coarse atom is the
disjoint union of the fine atoms which it contains.  Consequently its
indicator is their sum.  Linearity then transfers cut regularity, with the
number of contained fine atoms as the exact loss.  The same decomposition,
followed by finite Cauchy--Schwarz and a fiberwise sum, controls the
coarse-upper atom-energy gap by the fine-upper gap with only one fine
complexity factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse fibers of fine atoms -/



















/-! ## Linear transfer of cut regularity -/

















/-! ## Coarse-upper atom-energy gaps -/













namespace OrderedCoarseFineComplex

/-- The lower-boundary energy gap measured against the atoms of the
*coarse* upper face partition. -/
noncomputable def coarseUpperFaceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.coarse.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.coarse.partition j.succ e)





/-- The rank-`j` coarse-upper gap, summed over all ordered upper faces. -/
noncomputable def coarseUpperLayerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.coarse.partition j.succ)









end OrderedCoarseFineComplex

end Wikipedia.SzemeredisTheorem


