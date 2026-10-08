-- Prove2me | solution 1 for ProofsInTheBook.Chapter30.PathCountSystem.det_matrix_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:27:39.377924+00:00
-- url     : https://prove2.me/submissions/53edd407-c82d-487c-b1ac-37ff6fa9c3c0

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter30


/-!
# Chapter 30: Lattice paths and determinants

From "Proofs from THE BOOK":

**Lindström-Gessel-Viennot lemma**: The number of non-intersecting
lattice path systems from sources to sinks equals a determinant.

The book applies this to count standard Young tableaux and proves
the hook length formula: |SYT(λ)| = n! / ∏ hook_lengths.
-/

namespace ProofsInTheBook.Chapter30

open Matrix BigOperators











































namespace LGVBadFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]















end LGVBadFamily



namespace LGVFamily

variable {n : ℕ} {V R : Type*} [DecidableEq V]





















end LGVFamily





namespace PathCountSystem

variable {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]







end PathCountSystem







/-
Tiny compiled application of `chapter30`.

The current `PathCountSystem` still targets `LGVFamily n V`, whose paths are
unbounded `List V`s.  For a nonempty geometric vertex type this is not a finite
type without an additional bounded/geometric path layer, so full grid-path
applications such as the hook-length formula still require more infrastructure.
The empty-vertex case below is the smallest finite instance: there is one formal
path in every entry of a `2 × 2` path-count matrix, and the two signed
non-intersecting families cancel.
-/
namespace EmptyTwoByTwoExample



























end EmptyTwoByTwoExample

end ProofsInTheBook.Chapter30

open ProofsInTheBook.Chapter30
open Matrix BigOperators
open ProofsInTheBook.Chapter30.PathCountSystem
variable {n : ℕ} {V R : Type*} [DecidableEq V] [CommRing R]

theorem solution (S : PathCountSystem n V R) [Fintype (LGVFamily n V)] :
    S.matrix.det = ∑ F : LGVFamily n V, ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight F := by
  classical
  letI : ∀ i j : Fin n, Fintype (S.Path i j) := S.pathFintype
  have h_expand :
      S.matrix.det =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := by
    calc
      S.matrix.det =
          ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, S.matrix (σ i) i := by
            exact Matrix.det_apply S.matrix
      _ =
          ∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ •
              (∑ choice : (∀ i : Fin n, S.Path (σ i) i),
                ∏ i : Fin n, S.pathWeight (choice i)) := by
            apply Finset.sum_congr rfl
            intro σ _
            simp [matrix, pathCount, Fintype.prod_sum]
      _ =
          ∑ σ : Equiv.Perm (Fin n),
            ∑ choice : (∀ i : Fin n, S.Path (σ i) i),
              Equiv.Perm.sign σ • ∏ i : Fin n, S.pathWeight (choice i) := by
            simp [Finset.smul_sum]
      _ =
          ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
            Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := by
            exact
              (Fintype.sum_sigma'
                (fun σ (choice : ∀ i : Fin n, S.Path (σ i) i) =>
                  Equiv.Perm.sign σ • ∏ i : Fin n, S.pathWeight (choice i))).symm
  calc
    S.matrix.det =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          Equiv.Perm.sign X.1 • ∏ i : Fin n, S.pathWeight (X.2 i) := h_expand
    _ =
        ∑ X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i),
          ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight (S.familyEquiv X) := by
          apply Finset.sum_congr rfl
          intro X _
          exact (S.weight_eq X).symm
    _ = ∑ F : LGVFamily n V, ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight F := by
          simpa using
            (Fintype.sum_equiv S.familyEquiv
              (fun X : (Σ σ : Equiv.Perm (Fin n), ∀ i : Fin n, S.Path (σ i) i) =>
                ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight (S.familyEquiv X))
              (fun F : LGVFamily n V => ProofsInTheBook.Chapter30.LGVFamily.signedWeight S.vertexWeight F)
              (by intro X; rfl))
