-- Prove2me | Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_boundary_histograms
-- name    : mme_modern_CW_power_nonzero_coefficient_boundary_histograms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T05:17:41.205264+00:00
-- url     : https://prove2.me/theorems/8a23440c-3f62-463a-9496-cd1240acb37a
-- title:
--   Nonzero actual CW power coefficients force grouped full-word boundary histograms
-- statement:
--   Let $B=2^{\max(\ell-1,0)}$ and take a nonzero joint coordinate-word coefficient of the actual tensor $CW_q^{\otimes NB}$ over any field. Define each mode's entire fine word at chunk $t$ by $W_i(t)(r)=g(w_i(\operatorname{flatten}(t,r)))$, using the actual canonical CW coordinate grade. Group chunks by any map into outer owner cells, and suppose each full-word grade sum equals that cell's specified coarse grade. Inside each cell the exact full-word histograms obey
--
--   $$
--
--   Z=0:\ \#\{Y=\sigma\}=\#\{X=\mathbf2-\sigma\},\qquad
--   X=0:\ \#\{Z=\sigma\}=\#\{Y=\mathbf2-\sigma\},\qquad
--   Y=0:\ \#\{Z=\sigma\}=\#\{X=\mathbf2-\sigma\}.
--
--   $$
--
--   All counts refer to the same cell. Word complementation changes each grade to $2-a$ without permuting positions. The cells may group arbitrarily many fine words. Unlike the earlier boundary transfer interface, this theorem derives fine support from a nonzero coefficient of the actual source tensor; it does not assume source support or the desired compatibility predicate.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions 3.4–3.6 (printed pp. 14–15), Remark 5.2 and Claims 5.7/5.10 (pp. 19–24). Exact composition of the actual tensor-power coefficient factorization with the public full-word CW boundary theorem c67f96ff-f17e-435f-ab97-c96837e9cf85 (Proved in the pinned environment). Supplies the boundary portion of hSupportedY/hSupportedZ in the grouped coarse-owner restriction theorem c23eb8b9-f09c-439b-8ce9-b4a8e390bf4c. Coarse hash ownership and the other marginal-typicality conditions remain separate obligations.

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_modern_CW_full_word_boundary_histograms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

open MME MME.TensorObj MME.DWZStep1Support MME.CompleteSplit
open PiTensorProduct TensorProduct BigOperators Module

universe u v

set_option autoImplicit false

theorem mme_modern_CW_power_nonzero_coefficient_boundary_histograms
    {K : Type u} [Field K] (q ell N : ℕ)
    (w : Fin 3 → Fin (N * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2)))
    (hcoeff :
      (Basis.piTensorProduct (fun i ↦
        kronPowModeWordBasis (CWObj K q) i
          ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
          (N * 2 ^ (ell - 1)))).repr
        ((CWObj K q).kronPow (N * 2 ^ (ell - 1))).t w ≠ 0)
    {Cell : Type v} [DecidableEq Cell]
    (cell : Fin N → Cell) (coarse : Cell → Fin 3 → ℕ)
    (hCoarse : ∀ i t,
      ∑ r : Fin (2 ^ (ell - 1)),
        (cwSquareCoordGrade q (w i (finProdFinEquiv (t, r))).down).val =
          coarse (cell t) i) :
    let word : Fin 3 → Fin N → CompleteWord ell :=
      fun i t r ↦ cwSquareCoordGrade q (w i (finProdFinEquiv (t, r))).down
    (∀ s : Cell, coarse s 2 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 1 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 0 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 1 t = fun r ↦ Fin.rev (sigma r)}) ∧
    (∀ s : Cell, coarse s 1 = 0 → ∀ sigma : CompleteWord ell,
      Fintype.card {t : Fin N // cell t = s ∧ word 2 t = sigma} =
        Fintype.card {t : Fin N //
          cell t = s ∧ word 0 t = fun r ↦ Fin.rev (sigma r)}) := by sorry
