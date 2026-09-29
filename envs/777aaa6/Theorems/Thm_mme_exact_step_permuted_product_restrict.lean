-- Prove2me | Theorems.Thm_mme_exact_step_permuted_product_restrict
-- name    : mme_exact_step_permuted_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:13:01.71399+00:00
-- url     : https://prove2.me/theorems/ef3594f0-979e-4b55-80de-d7522323af21
-- title:
--   Exact hashing steps combine under whole-region permutations
-- statement:
--   A finite family of exact hashing steps gives a tensor restriction after permuting the modes of each whole region. Each factor retains its exact post-repair integer copy count. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_kronFin_mono_restrict
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_profiled_CW_all_mode_permutations_iso
import Theorems.Thm_mme_bigAdd_mono_restrict
open MME MME.TensorObj MME.ProfiledCW
universe u

theorem mme_exact_step_permuted_product_restrict {K : Type u} [Field K]
    {n ell : ℕ} (N : Fin n → ℕ) (P : ∀ r, Predicate (N r))
    (E : ∀ r, ExactStep ell (N r) (P r)) (sigma : Fin n → Equiv.Perm (Fin 3)) :
    Restrict
      (kronFin n (fun r => bigAdd (fun _ : Fin (E r).copies =>
        tensor K (fun i => (E r).output ((sigma r).symm i)))))
      (kronFin n (fun r => tensor K (fun i => P r ((sigma r).symm i)))) := by sorry
