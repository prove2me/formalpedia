-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.shared_degree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:23:20.543193+00:00
-- url     : https://prove2.me/submissions/a514d1c1-c7e2-4faf-b702-fa196c1468c8

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄) (P : E₁) :
    D.phiHat (D.psi'Hat (D.psi' (D.phi P))) = ((D.a * D.b : ℕ) : ℤ) • P := by
  rw [D.phiHat_psi'Hat, D.phi'Hat_psi', D.phiHat_phi, map_zsmul, map_zsmul, D.psiHat_psi,
    smul_smul]
  congr 1
