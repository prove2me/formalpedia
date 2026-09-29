-- Prove2me | Theorems.Thm_mme_dwz_table2_exact_outer_seven_eighths_has_nonhole
-- name    : mme_dwz_table2_exact_outer_seven_eighths_has_nonhole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:40:53.190037+00:00
-- url     : https://prove2.me/theorems/12c78a74-ef3e-43f5-bf47-376eac1d66a9
-- title:
--   A Claim-6.8 certificate yields a literal nonhole Table-2 useful block
-- statement:
--   Let an outer word have the exact Table-2 component profile at multiplier $m$, and let $C$ be a broken copy on its literal useful fine-$Z$ blocks. If Claim 6.8's exact division-free certificate
--
--   $$7|B| \le 8|C_{\mathrm{nonhole}}|$$
--
--   holds, then there is an actual useful block in $C_{\mathrm{nonhole}}$. Because exact-profile useful blocks are independently known to exist, this conclusion is nonvacuous even in the presence of zero split cells.
--
--   Applied to every retained outer word in Claim 6.8, the theorem provides one literal surviving fine-$Z$ block per copy.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 6.3 and Claim 6.8; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_seven_eighths_certificate_has_literal_nonhole
import Theorems.Thm_mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty

set_option autoImplicit false

theorem mme_dwz_table2_exact_outer_seven_eighths_has_nonhole
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
  sorry
