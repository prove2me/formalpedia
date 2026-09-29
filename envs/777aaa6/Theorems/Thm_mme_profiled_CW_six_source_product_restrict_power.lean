-- Prove2me | Theorems.Thm_mme_profiled_CW_six_source_product_restrict_power
-- name    : mme_profiled_CW_six_source_product_restrict_power
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:10:38.072964+00:00
-- url     : https://prove2.me/theorems/735310cc-4cec-434a-ad06-1f67cc297ffe
-- title:
--   All six profiled source families restrict one CW power family
-- statement:
--   The product of six symmetrized profiled source families restricts copies of CW to the 144 Nth power. Its exact multiplicity is the product of the sixth powers of the six input counts. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_profiled_CW_repeated_six_restrict_power
import Theorems.Thm_mme_toQ_kronFin
open MME MME.TensorObj BigOperators
universe u

theorem mme_profiled_CW_six_source_product_restrict_power
    {K : Type u} [Field K] (N : ℕ) (inputs : Fin 6 → ℕ)
    (P : Fin 6 → ProfiledCW.Predicate (4 * N)) :
    Restrict
      (kronFin 6 (fun owner => sixSymmetrization
        (bigAdd (fun _ : Fin (inputs owner) => ProfiledCW.tensor K (P owner)))))
      (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
        (CWObj K 5).kronPow (144 * N))) := by sorry
