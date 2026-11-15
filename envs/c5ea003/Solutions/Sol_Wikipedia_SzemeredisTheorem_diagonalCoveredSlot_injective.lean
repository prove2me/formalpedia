-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.diagonalCoveredSlot_injective
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:52.648291+00:00
-- url     : https://prove2.me/submissions/0d30d65e-0f7b-406b-bf35-a9c7aefba7ab

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eq_of_deletedVectorToFinTuple_eq_of_sum_eq

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





















/-- Distinct degenerate AP parameters give distinct labelled simplices. -/
theorem diagonalAPSimplex_injective
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (diagonalAPSimplex r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have hmoment :=
      congrArg
        (simplexCoordinateMoment (r + 2) N) hpq
    simpa using hmoment
  · funext i
    exact congrFun hpq i.succ.succ







namespace SimplexHypergraph







end SimplexHypergraph

























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
/-- No deleted coloured face can cover two different members of the
degenerate simplex family.  Equality off the deleted coordinate and equality
of the total coordinate sums recover the whole labelled simplex. -/
theorem solution
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Function.Injective
      (diagonalCoveredSlot r N A deleted hcover) := by
  intro p q hpq
  apply diagonalAPSimplex_injective r N A
  apply eq_of_deletedVectorToFinTuple_eq_of_sum_eq
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A p) =
        simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A q)
    simp
