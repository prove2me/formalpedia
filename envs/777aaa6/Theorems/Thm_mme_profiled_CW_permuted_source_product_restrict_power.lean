-- Prove2me | Theorems.Thm_mme_profiled_CW_permuted_source_product_restrict_power
-- name    : mme_profiled_CW_permuted_source_product_restrict_power
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T22:27:26.075793+00:00
-- url     : https://prove2.me/theorems/ebcc7deb-ff89-4df1-b747-49cc1cb92c80
-- title:
--   Permuted source families transfer to CW powers
-- statement:
--   Let $K$ be a field, let $N$ be a nonnegative integer, and take six profiled source families with input counts $m_i$ and arbitrary permutations of their three tensor modes. After sixfold symmetrization, their product is a restriction of a direct sum of $\prod_{i=1}^{6}m_i^6$ copies of the $144N$th tensor power of $CW_5$. This preserves the exact source multiplicity when transferring the outer extraction to elementary CW powers.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_profiled_CW_six_source_product_restrict_power
import Theorems.Thm_mme_sixSymmetrization_mode_permutation_iso
import Theorems.Thm_mme_kronFin_mono_restrict
import Definitions.Def_mme_cyclicSymmetrization_public_perm
open MME MME.TensorObj
open scoped BigOperators
universe u

theorem mme_profiled_CW_permuted_source_product_restrict_power
    {K : Type u} [Field K] (N : ℕ) (inputs : Fin 6 → ℕ)
    (P : Fin 6 → ProfiledCW.Predicate (4 * N))
    (sigma : Fin 6 → Equiv.Perm (Fin 3)) :
    Restrict
      (sixSymmetrization (kronFin 6 (fun owner => permObj (sigma owner)
        (bigAdd (fun _ : Fin (inputs owner) => ProfiledCW.tensor K (P owner))))))
      (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
        (CWObj K 5).kronPow (144 * N))) := by sorry
