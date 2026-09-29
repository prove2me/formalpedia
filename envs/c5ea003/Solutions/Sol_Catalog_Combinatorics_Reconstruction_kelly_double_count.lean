-- Prove2me | solution 1 for Catalog.Combinatorics.Reconstruction.kelly_double_count
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:15:19.034208+00:00
-- url     : https://prove2.me/submissions/8d79e93a-afa8-4f4b-82b3-717b1f512a86

-- Sol generated from Combinatorics/Reconstruction.lean
import Mathlib
import Definitions.Def_Combinatorics_Reconstruction

/-!
# Vertex-deleted decks and Kelly's counting lemma

The full reconstruction conjecture is open.  This file develops its standard
finite-graph language, proves the double-counting core of Kelly's lemma, and
proves reconstruction for the two extremal graph classes: edgeless and complete
graphs.
-/

open Catalog.Combinatorics.Reconstruction

open Finset SimpleGraph
open scoped Sym2

variable {V W U : Type*}















/-!
# Complement compatibility for vertex decks

Taking graph complements preserves and reflects equality of vertex-deleted decks.
-/

open Catalog.Combinatorics.Reconstruction

open SimpleGraph

variable {V W : Type*}






open Catalog.Combinatorics.Reconstruction in
theorem solution[Fintype V] [DecidableEq V]
    (A : Finset (Finset V)) (k : ℕ) (hA : UniformFamily A k) :
    ∑ v : V, (survivingSets A v).card = (Fintype.card V - k) * A.card := by
  have h1 : ∑ v : V, (survivingSets A v).card = ∑ s ∈ A, (Fintype.card V - k) := by
    simp_rw [survivingSets, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    have hsk : s.card = k := hA s hs
    rw [Finset.sum_ite]
    simp
    rw [show (Finset.univ.filter fun x => x ∉ s) = Finset.univ \ s from by ext; simp]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ, hsk]
  rw [h1, Finset.sum_const, Finset.card_eq_sum_ones, smul_eq_mul, mul_comm]
