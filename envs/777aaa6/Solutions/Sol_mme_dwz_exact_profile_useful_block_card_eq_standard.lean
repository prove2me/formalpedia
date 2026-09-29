-- Prove2me | solution 1 for mme_dwz_exact_profile_useful_block_card_eq_standard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T21:02:39.100909+00:00
-- url     : https://prove2.me/submissions/fae65478-cdc0-4ba7-930d-cc434162b863

import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (houter : ∀ s : Fin 15,
      Fintype.card {r : Fin N // outer r = s} =
        MME.DWZTable2Counts.component s * m) :
    Fintype.card (MME.DWZTable2StandardForm.UsefulBlock m outer) =
      Fintype.card (MME.DWZComponentRestriction.DWZStandardBlock m) := by
  classical
  let emptyCopy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer) := ⟨∅⟩
  obtain ⟨_positionEquiv, _hposition, blockEquiv, _hblock,
      _transported, _hcard, _hmem⟩ :=
    mme_dwz_table2_broken_copy_transport_to_standard
      outer houter emptyCopy
  exact Fintype.card_congr blockEquiv
