-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eq_of_deletedVectorToFinTuple_eq_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:24:40.140212+00:00
-- url     : https://prove2.me/submissions/f311ecd0-7db0-449d-8cb4-a1ab966950f7

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

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















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
/-- A full tuple is determined by one deleted-coordinate tuple together
with its total sum. -/
theorem solution
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (hjl : j = l)
    (hdeleted :
      deletedVectorToFinTuple j (deleteCoordinate x j) =
        deletedVectorToFinTuple l (deleteCoordinate y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have hother :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [hother]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
