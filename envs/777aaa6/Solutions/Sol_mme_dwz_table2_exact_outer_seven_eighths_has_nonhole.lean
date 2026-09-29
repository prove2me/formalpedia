-- Prove2me | solution 1 for mme_dwz_table2_exact_outer_seven_eighths_has_nonhole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:41:14.666531+00:00
-- url     : https://prove2.me/submissions/1e290875-2c04-4ef1-a255-1a4cf54b6c99

import Theorems.Thm_mme_dwz_seven_eighths_certificate_has_literal_nonhole
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Position : Type*}
    [Fintype Position] [DecidableEq Position]
    (outer : Position → Fin 15)
    (hProfile : ∀ s : Fin 15,
      Fintype.card {t : Position // outer t = s} =
        MME.DWZTable2Counts.component s * m)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m outer))
    (hseven :
      7 * Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m outer) ≤
        8 * copy.nonholes.card) :
    ∃ small : MME.DWZTable2StandardForm.UsefulBlock m outer,
      small ∈ copy.nonholes := by
  letI : Nonempty (MME.DWZTable2StandardForm.UsefulBlock m outer) :=
    mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty m outer hProfile
  exact mme_dwz_seven_eighths_certificate_has_literal_nonhole copy hseven
