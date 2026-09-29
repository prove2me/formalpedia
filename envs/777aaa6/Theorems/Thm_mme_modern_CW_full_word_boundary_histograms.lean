-- Prove2me | Theorems.Thm_mme_modern_CW_full_word_boundary_histograms
-- name    : mme_modern_CW_full_word_boundary_histograms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:00:33.039724+00:00
-- url     : https://prove2.me/theorems/c67f96ff-f17e-435f-ab97-c96837e9cf85
-- title:
--   Actual CW fine support transfers complete-word histograms on zero-grade boundary cells
-- statement:
--   Let a finite set of chunk positions be grouped by an arbitrary cell map. In each mode, each position carries its entire level-$\ell$ fine word, and the sum of its fine grades equals that cell's specified coarse grade. Assume every position and fine letter gives a nonzero block of the actual canonical three-grading of $CW_q$, over any field. On each zero-grade boundary cell, the exact full-word histograms satisfy
--   $
--   Z=0:\ \#\{Y=\sigma\}=\#\{X=\mathbf2-\sigma\},\qquad
--   X=0:\ \#\{Z=\sigma\}=\#\{Y=\mathbf2-\sigma\},\qquad
--   Y=0:\ \#\{Z=\sigma\}=\#\{X=\mathbf2-\sigma\}.
--   $
--   Every count is restricted to the same cell. Complementing a word changes each grade $a$ to $2-a$ without changing its position. The cell map is arbitrary and need not be injective: all fine words inside the same owner cell remain grouped, and empty cells are included. This derives the boundary histogram transfer from actual CW source support; it does not assume the desired Y/Z compatibility predicate or assert a complete global extraction.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2 (2024-10-20), Remark 5.2, Definition 5.6 and Claim 5.7 on printed pp. 19–23, and Definition 5.9/Claim 5.10 on p. 24, https://arxiv.org/abs/2404.16349v2. Generalizes the actual-source boundary-fiber argument from the proved DWZ Table2 boundary histogram theorem to full ordered words, arbitrary grouped cells, and all three relevant boundary orientations. Uses the public actual CW canonical support theorem af5087e0-64d7-4375-9091-9a23a4197be2. This is the boundary component of the compatibility/ownership bridge; coefficient-to-pointwise support, coarse hash ownership, and the remaining marginal-typicality conditions are separate obligations.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Mathlib.Data.Fin.Rev

open MME MME.CompleteSplit MME.DWZStep1Support BigOperators

universe u v w

set_option autoImplicit false

theorem mme_modern_CW_full_word_boundary_histograms
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
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) := by sorry
