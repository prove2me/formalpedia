-- Prove2me | Theorems.Thm_mme_stothers_cwFourth_swapped_block_iso
-- name    : mme_stothers_cwFourth_swapped_block_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:58:02.272934+00:00
-- url     : https://prove2.me/theorems/0c41b609-9bee-4480-9178-dddbaba941de
-- title:
--   Canonical fourth CW blocks are equivariant under a mode transposition
-- statement:
--   Let $T_q^{\otimes 4}$ carry its canonical grading by the nine total CW grades $0,\ldots,8$, and let $T_\rho$ denote the block selected by an ordered grade triple $\rho$.  If $s$ exchanges the first two tensor modes, then the block selected by the relabelled triple $\rho\circ s^{-1}$ is tensor-isomorphic to the mode-transposed original block:
--
--   $$T_{\rho\circ s^{-1}}\cong s\cdot T_\rho.$$
--
--   The result is uniform in the CW parameter $q$ and supplies the literal tensor-level equivariance needed to compare the two orientations inside each six-element permutation class in the Davie--Stothers fourth-power analysis.
-- source:
--   The tensor-mode symmetry of the fourth Coppersmith--Winograd power used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_oriented_cyclic_classes

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_cwFourth_swapped_block_iso
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        (MME.StothersFourth.fixedModeRelabel swapFirstTwoPerm ρ))
      (TensorObj.permObj swapFirstTwoPerm
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
          ρ)) := by
  sorry
