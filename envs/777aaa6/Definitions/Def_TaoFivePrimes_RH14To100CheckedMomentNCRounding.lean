-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCRounding
-- name    : TaoFivePrimes_RH14To100CheckedMomentNCRounding
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-22T09:51:02.177689+00:00
-- url     : https://prove2.me/theorems/4eded1d6-7317-4896-ab9b-635be97c83b5
-- title:
--   RH height 14–100 — certified moment data rounding
-- statement:
--   The proposed integer moment list, constructed as CheckedRounding with a kernel-checked equality to the exact rounded sum of the sixteen convolution records. This equality is the required validity field of the numeric data record; it asserts no analytic integral estimate.
--
--   **Port note.** This is a port, to the Mathlib `777aaa6` / Lean v4.29.0-rc3 environment of the Riemann Hypothesis mission tree, of the definition `TaoFivePrimes_RH14To100CheckedMomentNCRounding` (id `0210e3cb-d32f-4c8a-9ccb-d44f1e6e78aa`, env `0df444a`, published by @raresbuhai). The Lean source is unchanged.
-- source:
--   sometik179, original height-14–100 certificate c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; original theta/Mellin foundations attributed to Gabewhigham. These same ordinary data and Boolean kernel validations occur in public moment-enclosure submission 821c0bfb-a758-4f7c-8bd3-e2b55ae05d26. The packet constructor validity proofs are necessary fields of dependent data structures; the substantive analytic enclosure remains a separate theorem.; ported from 0df444a definition 0210e3cb-d32f-4c8a-9ccb-d44f1e6e78aa

/- Proof-bearing finite certificate data from sometik179's original
height-14–100 certificate; theta/Mellin attribution to Gabewhigham. The Boolean
validity proof is a necessary constructor field, checked by the Lean kernel. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentCertificateDataNC
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
namespace RH14MomentCertificateData
open RH14MomentEnclosureProof.CertifiedMomentRecords
noncomputable def rounding : CheckedRounding :=
  ⟨roundedNumerators, by decide +kernel⟩
end RH14MomentCertificateData
def TaoFivePrimes_RH14To100CheckedMomentNCRounding : Nat := 14


