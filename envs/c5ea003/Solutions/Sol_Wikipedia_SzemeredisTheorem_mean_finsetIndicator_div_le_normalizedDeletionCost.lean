-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_finsetIndicator_div_le_normalizedDeletionCost
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:55:02.855903+00:00
-- url     : https://prove2.me/submissions/24bb15ee-07c7-4c2f-8542-865822607ff1

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_diagonalAPParameter_le_deletionCount

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









theorem mean_finsetIndicator {α : Type*}
    [Fintype α] [DecidableEq α] (A : Finset α) :
    mean (finsetIndicator A) =
      (A.card : ℝ) / Fintype.card α := by
  rw [mean, Fintype.expect_eq_sum_div_card]
  simp [finsetIndicator]

























end Wikipedia.SzemeredisTheorem

end

section





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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





























namespace SimplexHypergraph







end SimplexHypergraph















/-- For constant vertex classes `ZMod N`, the total number of coloured face
slots is `(r+2) N^(r+1)`. -/
@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]









end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- A simplex cover of the AP-set hypergraph has normalized deletion cost at
least one `1/(r+2)` share of the density of `A`.  This is the exact
edge-disjoint-degenerate-simplices estimate used in the removal argument. -/
theorem solution
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by
  have hcount :
      A.card * N ^ r ≤
        SimplexHypergraph.deletionCount deleted := by
    simpa using
      card_diagonalAPParameter_le_deletionCount
        r N A deleted hcover
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [mean_finsetIndicator, ZMod.card,
    SimplexHypergraph.normalizedDeletionCost,
    deletionCapacity_zmod]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (SimplexHypergraph.deletionCount deleted : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity
