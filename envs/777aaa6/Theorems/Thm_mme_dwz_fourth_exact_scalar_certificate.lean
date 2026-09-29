-- Prove2me | Theorems.Thm_mme_dwz_fourth_exact_scalar_certificate
-- name    : mme_dwz_fourth_exact_scalar_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T08:22:59.864471+00:00
-- url     : https://prove2.me/theorems/2710bd43-45ef-4fee-9ed1-dda793c6ee5e
-- title:
--   Soundness of every retained-floor obligation of the scalar ledger
-- statement:
--   Every rational entropy bracket in the fourth-power ledger holds for the real entropy, and every retained-floor obligation holds over the reals.
--
--   For a record whose cells point at log-table entries with arguments $x_1,\dots,x_k$, the real entropy is $\mathrm{entropyActual} = \sum_j -x_j \log x_j$. The statement says:
--
--   1. For each of the 1589 entropy records, this real entropy lies between the record's rational `lowerFloor` and `upperCeiling`.
--   2. For each of the 204 retained-floor obligations, the obligation's linear combination of record entropies (`termsActual`) is defined, and the rational retained floor is at most its constant plus that real value.
--
--   This moves the rational arithmetic checked in `mme_dwz_fourth_exact_retained_entropy_arithmetic` over to real entropies, using the pointwise logarithm bounds of `mme_dwz_fourth_log_lookup_sound`.
--
--   The statement is the conjunction of 2 facts about this stage of the fourth-power assembly:
--
--   (1) stated in Lean as
--
--   ```lean
--   ∀ (i : Fin entropyRecords.size),
--     ((entropyRecords[i]).lowerFloor : ℝ) ≤
--         entropyActual (entropyRecords[i]).cells ∧
--       entropyActual (entropyRecords[i]).cells ≤
--         ((entropyRecords[i]).upperCeiling : ℝ)
--   ```
--
--   (2) stated in Lean as
--
--   ```lean
--   ∀ (i : Fin obligations.size),
--     ∃ actual, termsActual (obligations[i]).terms = some actual ∧
--       ((obligations[i]).retainedFloor : ℝ) ≤
--         ((obligations[i]).constant : ℝ) + actual
--   ```
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_exact_scalar_certificate_data
import Theorems.Thm_mme_dwz_fourth_exact_retained_entropy_arithmetic
import Theorems.Thm_mme_dwz_fourth_log_lookup_sound

open MME MME.DWZFourthExactScalarCertificate
open MME
open MME.DWZFourthLogScaleTable
open MME.DWZFourthRetainedEntropy
open scoped Classical

set_option autoImplicit false

theorem mme_dwz_fourth_exact_scalar_certificate :
    (∀ (i : Fin entropyRecords.size),
      ((entropyRecords[i]).lowerFloor : ℝ) ≤
          entropyActual (entropyRecords[i]).cells ∧
        entropyActual (entropyRecords[i]).cells ≤
          ((entropyRecords[i]).upperCeiling : ℝ)) ∧
    (∀ (i : Fin obligations.size),
      ∃ actual, termsActual (obligations[i]).terms = some actual ∧
        ((obligations[i]).retainedFloor : ℝ) ≤
          ((obligations[i]).constant : ℝ) + actual) := by sorry
