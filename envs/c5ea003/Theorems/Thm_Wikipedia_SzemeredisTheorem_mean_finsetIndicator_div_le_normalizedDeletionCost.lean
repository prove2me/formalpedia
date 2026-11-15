-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_finsetIndicator_div_le_normalizedDeletionCost
-- name    : Wikipedia.SzemeredisTheorem.mean_finsetIndicator_div_le_normalizedDeletionCost
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:56.910581+00:00
-- url     : https://prove2.me/theorems/ac2def14-2996-452a-ac8a-efcef35a61d4
-- title:
--   A simplex cover costs a share of the set density
-- statement:
--   Let $r\ge0$ and $N\ge1$ be integers, and let $A\subseteq\mathbb Z/N\mathbb Z$. Suppose a deletion family $\mathcal D$ is a simplex cover of the $(r+2)$-partite AP-set hypergraph associated with $A$. Its normalized deletion cost satisfies
--   $$
--   \frac{\mathbb E\,1_A}{r+2}\le\operatorname{cost}(\mathcal D).
--   $$
--   Thus covering all simplices costs at least one $(r+2)^{-1}$ share of the normalized density of $A$. The estimate does not require a factorial-coprimality condition on $N$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/APRemoval.lean#L401-L436

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
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
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_finsetIndicator_div_le_normalizedDeletionCost
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by sorry
