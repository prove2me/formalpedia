-- Prove2me | solution 1 for ProofsInTheBook.Chapter30.total_sum_eq_good_sum_of_bad_sign_reversing
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:27:43.7968+00:00
-- url     : https://prove2.me/submissions/350c531a-b39a-4346-8d7b-0bec75ad686e

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





/--
Finite sign-reversing reindexing lemma.

In an arbitrary additive group this gives `S = -S`, not necessarily `S = 0`
unless the target has no `2`-torsion.
-/
theorem sum_eq_neg_self_of_sign_reversing_equiv {α R : Type*} [Fintype α]
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

/-- A sign-reversing involution makes the total signed sum `2`-torsion. -/
theorem two_nsmul_sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] (τ : α ≃ α) (w : α → R) (hw : ∀ x, w (τ x) = -w x) :
    (2 : ℕ) • (∑ x : α, w x) = 0 := by
  classical
  let S : R := ∑ x : α, w x
  have h : S = -S := by
    simpa [S] using sum_eq_neg_self_of_sign_reversing_equiv τ w hw
  change (2 : ℕ) • S = 0
  rw [two_nsmul]
  nth_rewrite 1 [h]
  exact neg_add_cancel S

/-- A sign-reversing involution cancels the sum in an additive torsion-free target. -/
theorem sum_eq_zero_of_sign_reversing_equiv {α R : Type*} [Fintype α]
    [AddCommGroup R] [IsAddTorsionFree R] (τ : α ≃ α) (w : α → R)
    (hw : ∀ x, w (τ x) = -w x) :
    (∑ x : α, w x) = 0 := by
  classical
  have h2 := two_nsmul_sum_eq_zero_of_sign_reversing_equiv τ w hw
  rcases (nsmul_eq_zero_iff.mp h2) with hsum | htwo
  · exact hsum
  · norm_num at htwo

































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
    [DecidableEq α] [AddCommGroup R] [IsAddTorsionFree R]
    (bad : α → Prop) [DecidablePred bad] (τbad : {x : α // bad x} ≃ {x : α // bad x})
    (w : α → R) (hw : ∀ x : {x : α // bad x}, w (τbad x).1 = -w x.1) :
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := by
  classical
  let badSet : Finset α := Finset.univ.filter fun x : α => bad x
  let goodSet : Finset α := Finset.univ.filter fun x : α => ¬ bad x
  have hbad_sum : (∑ x ∈ badSet, w x) = 0 := by
    let wbad : {x : α // bad x} → R := fun x => w x.1
    have hwbad : ∀ x : {x : α // bad x}, wbad (τbad x) = -wbad x := by
      intro x
      exact hw x
    have h := sum_eq_zero_of_sign_reversing_equiv τbad wbad hwbad
    have hfilter : (∑ x ∈ badSet, w x) = ∑ x : {x : α // bad x}, wbad x := by
      rw [← Finset.sum_subtype]
      simp [badSet]
    rw [hfilter, h]
  have huniv : (Finset.univ : Finset α) = badSet ∪ goodSet := by
    ext x
    by_cases hx : bad x <;> simp [badSet, goodSet, hx]
  have hdisj : Disjoint badSet goodSet := by
    rw [Finset.disjoint_left]
    intro x hxbad hxgood
    simp [badSet] at hxbad
    simp [goodSet, hxbad] at hxgood
  calc
    (∑ x : α, w x) = ∑ x ∈ (Finset.univ : Finset α), w x := by simp
    _ = ∑ x ∈ badSet ∪ goodSet, w x := by rw [huniv]
    _ = (∑ x ∈ badSet, w x) + ∑ x ∈ goodSet, w x := by
      rw [Finset.sum_union hdisj]
    _ = ∑ x ∈ goodSet, w x := by rw [hbad_sum, zero_add]
    _ = ∑ x ∈ (Finset.univ.filter fun x : α => ¬ bad x), w x := rfl
