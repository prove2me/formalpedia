-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.normalizedDeletionCost_orderedDeletionToSimplex_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:06.719842+00:00
-- url     : https://prove2.me/submissions/f9da9a35-cb02-4222-a1c2-d6df650ab059

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
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators































/-- Reindexing a deletion face does not change its cardinality. -/
@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple



/-- The deletion density of a transported colour is its ordered-face
density. -/
theorem colorDeletionDensity_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (orderedDeletionToSimplex D) j =
      OrderedPattern.faceDeletionDensity
        D (orderedFacet j) := by
  rw [SimplexHypergraph.colorDeletionDensity,
    OrderedPattern.faceDeletionDensity,
    card_orderedDeletionToSimplex]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedVectorFinTupleEquiv j)
  rw [hcard]







end Wikipedia.SzemeredisTheorem

end
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
/-- Uniform ordered-face density bounds imply the same bound for total
normalized simplex deletion cost. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε) :
    SimplexHypergraph.normalizedDeletionCost
        (orderedDeletionToSimplex D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedVectorFinTupleEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((orderedDeletionToSimplex D j).card : ℝ) ≤
        ε * M := by
    have hdensity :=
      colorDeletionDensity_orderedDeletionToSimplex D j
    have hbound := hD (orderedFacet j)
    rw [← hdensity] at hbound
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hbound
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hbound
  have hcount :
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((orderedDeletionToSimplex D j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (ε * M) := by
        simp
  have hcapacity :
      SimplexHypergraph.deletionCapacity
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold SimplexHypergraph.deletionCapacity
    simp_rw [hface]
    simp
  rw [SimplexHypergraph.normalizedDeletionCost,
    hcapacity]
  have hdenom :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ hdenom).2
  calc
    (SimplexHypergraph.deletionCount
        (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := hcount
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring
