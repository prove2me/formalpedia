-- Prove2me | solution 1 for mme_modern_CW_full_word_boundary_histograms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:03:59.167111+00:00
-- url     : https://prove2.me/submissions/b396b667-9d24-4eb6-92a1-2b981d0df919

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Theorems.Thm_mme_CW_three_canonical_support
import Mathlib.Data.Fin.Rev

open MME MME.CompleteSplit MME.DWZStep1Support BigOperators

universe u v w

set_option autoImplicit false
set_option warningAsError true

private theorem fine_support_sum
    {K : Type u} [Field K] (q : ℕ) {ell : ℕ}
    {Position : Type v}
    (word : Fin 3 → Position → CompleteWord ell)
    (hSupport : ∀ t r,
      (cwThreeCanonicalGrading K q).blockTensor (fun i ↦ word i t r) ≠ 0)
    (t : Position) (r : Fin (2 ^ (ell - 1))) :
    (word 0 t r).val + (word 1 t r).val + (word 2 t r).val = 2 := by
  by_contra h
  exact hSupport t r (mme_CW_three_canonical_support K q (fun i ↦ word i t r) h)

private theorem word_grade_zero
    {ell : ℕ} {Position : Type v} {Cell : Type w}
    (cell : Position → Cell) (coarse : Cell → Fin 3 → ℕ)
    (word : Fin 3 → Position → CompleteWord ell)
    (hCoarse : ∀ i t, ∑ r, (word i t r).val = coarse (cell t) i)
    (s : Cell) (i : Fin 3) (hi : coarse s i = 0)
    (t : Position) (ht : cell t = s) (r : Fin (2 ^ (ell - 1))) :
    (word i t r).val = 0 := by
  have hsum : ∑ r, (word i t r).val = 0 := by
    rw [hCoarse i t, ht, hi]
  have hle : (word i t r).val ≤ ∑ a, (word i t a).val :=
    Finset.single_le_sum (f := fun a ↦ (word i t a).val)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
  omega

private theorem complement_histogram
    {ell : ℕ} {Position : Type v} [Fintype Position]
    {Cell : Type w} [DecidableEq Cell]
    (cell : Position → Cell) (source target : Position → CompleteWord ell)
    (s : Cell)
    (hComplement : ∀ t, cell t = s → target t = fun r ↦ Fin.rev (source t r))
    (sigma : CompleteWord ell) :
    Fintype.card {t : Position // cell t = s ∧ target t = sigma} =
      Fintype.card {t : Position //
        cell t = s ∧ source t = fun r ↦ Fin.rev (sigma r)} := by
  classical
  apply Fintype.card_congr
  refine {
    toFun := fun t ↦ ⟨t.1, t.2.1, ?_⟩
    invFun := fun t ↦ ⟨t.1, t.2.1, ?_⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }
  · funext r
    apply Fin.rev_injective
    simpa only [Fin.rev_rev] using
      (congrFun (hComplement t.1 t.2.1) r).symm.trans (congrFun t.2.2 r)
  · funext r
    calc
      target t.1 r = Fin.rev (source t.1 r) := congrFun (hComplement t.1 t.2.1) r
      _ = Fin.rev (Fin.rev (sigma r)) := congrArg Fin.rev (congrFun t.2.2 r)
      _ = sigma r := Fin.rev_rev _

/-- The full-word boundary reflection behind More Asymmetry Claims5.7 and5.10.
The source support is the actual fine CW block support, not an assumed
compatibility predicate; each cell can contain arbitrarily many fine words. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) {ell : ℕ}
    {Position : Type v} [Fintype Position]
    {Cell : Type w} [DecidableEq Cell]
    (cell : Position → Cell) (coarse : Cell → Fin 3 → ℕ)
    (word : Fin 3 → Position → CompleteWord ell)
    (hCoarse : ∀ i t, ∑ r, (word i t r).val = coarse (cell t) i)
    (hFineSupport : ∀ t r,
      (cwThreeCanonicalGrading K q).blockTensor (fun i ↦ word i t r) ≠ 0) :
    (∀ s : Cell, coarse s 2 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Position // cell t = s ∧ word 1 t = sigma} =
        Fintype.card {t : Position //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 0 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Position // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Position //
          cell t = s ∧ word 1 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 1 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Position // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Position //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) := by
  have hs := fine_support_sum q word hFineSupport
  refine ⟨?_, ?_, ?_⟩
  · intro s hzero sigma
    apply complement_histogram cell (word 0) (word 1) s _ sigma
    intro t ht
    funext r
    apply Fin.ext
    have hz := word_grade_zero cell coarse word hCoarse s 2 hzero t ht r
    have h := hs t r
    simp only [Fin.val_rev]
    omega
  · intro s hzero sigma
    apply complement_histogram cell (word 1) (word 2) s _ sigma
    intro t ht
    funext r
    apply Fin.ext
    have hz := word_grade_zero cell coarse word hCoarse s 0 hzero t ht r
    have h := hs t r
    simp only [Fin.val_rev]
    omega
  · intro s hzero sigma
    apply complement_histogram cell (word 0) (word 2) s _ sigma
    intro t ht
    funext r
    apply Fin.ext
    have hz := word_grade_zero cell coarse word hCoarse s 1 hzero t ht r
    have h := hs t r
    simp only [Fin.val_rev]
    omega
