-- Prove2me | Theorems.Thm_mme_stothers_cwFourth_cyclic_swapped_block_iso
-- name    : mme_stothers_cwFourth_cyclic_swapped_block_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:34:15.241502+00:00
-- url     : https://prove2.me/theorems/cbc2915f-e87b-4cda-9a71-db2fea0c8ef2
-- title:
--   A swapped fourth-power cyclic block is the mode swap of the original cyclic block
-- statement:
--   Let $T_{\rho}$ be the literal block of the canonical nine-grading of the fourth Coppersmith--Winograd power at ordered grade triple $\rho$.  Cyclically symmetrizing the block at the first-two-mode transpose of $\rho$ is tensor-isomorphic to applying that mode transpose to the cyclic symmetrization of $T_{\rho}$.  The statement is uniform in the Coppersmith--Winograd parameter $q$ and records both the mode symmetry of the literal fourth power and the conjugation of the cyclic orbit by a transposition.
-- source:
--   The tensor-mode symmetry used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5 and Table 1, pp. 366--368; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_oriented_cyclic_classes

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_cwFourth_cyclic_swapped_block_iso
    {K : Type u} [Field K] (q : ℕ) (ρ : Fin 3 → Fin 9) :
    TensorObj.Isomorphic
      (cyclicSymmetrization
        ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
          (MME.StothersFourth.fixedModeRelabel swapFirstTwoPerm ρ)))
      (TensorObj.permObj swapFirstTwoPerm
        (cyclicSymmetrization
          ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
            ρ))) := by
  sorry
