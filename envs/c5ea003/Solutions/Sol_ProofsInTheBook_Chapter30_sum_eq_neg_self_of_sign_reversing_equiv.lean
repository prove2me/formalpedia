-- Prove2me | solution 1 for ProofsInTheBook.Chapter30.sum_eq_neg_self_of_sign_reversing_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:31:46.40488+00:00
-- url     : https://prove2.me/submissions/1bfa721c-12bd-4504-a5ff-878ab7a058d3

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

theorem solution {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = -∑ x : α, w x := by
  classical
  have hreindex : (∑ x : α, w (τ x)) = ∑ x : α, w x := by
    simpa using
      (Fintype.sum_equiv τ
        (fun x : α => w (τ x))
        (fun y : α => w y)
        (by intro x; rfl))
  calc
    (∑ x : α, w x) = ∑ x : α, w (τ x) := hreindex.symm
    _ = ∑ x : α, -w x := by simp [hw]
    _ = -∑ x : α, w x := by simp
