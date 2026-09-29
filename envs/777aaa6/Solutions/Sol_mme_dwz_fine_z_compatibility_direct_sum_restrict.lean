-- Prove2me | solution 1 for mme_dwz_fine_z_compatibility_direct_sum_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T20:19:19.138704+00:00
-- url     : https://prove2.me/submissions/9b9bfd50-72d7-4276-818b-2b972319ed7b

import Theorems.Thm_mme_dwz_fine_z_owner_exists_of_unique_compatibility
import Theorems.Thm_mme_dwz_fine_z_unique_owner_direct_sum_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t N k : ℕ}
    (G : T.TypeGrading t)
    (fineAddress : Fin k → Fin 3 → Fin N → Fin t)
    (compatible : (Fin N → Fin t) → Fin k → Prop)
    [DecidableRel compatible]
    (hTargetCompatible : ∀ j : Fin k,
      compatible (fineAddress j 2) j)
    (hTargetUnique : ∀ j j' : Fin k,
      compatible (fineAddress j 2) j' → j' = j)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      js 0 = js 1)
    (hSupportedCompatible : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ fineAddress (js i) i r) ≠ 0) →
      compatible (fineAddress (js 2) 2) (js 0)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ gradedAddressBlock G (fineAddress j)))
      (T.kronPow N) := by
  rcases mme_dwz_fine_z_owner_exists_of_unique_compatibility
      G fineAddress compatible hTargetCompatible hTargetUnique
      hSupportedCompatible with
    ⟨fineZOwner, _, _, hOwned, hSupportedFineZOwner⟩
  exact mme_dwz_fine_z_unique_owner_direct_sum_restrict
    G fineAddress fineZOwner hOwned hXYOwner hSupportedFineZOwner
