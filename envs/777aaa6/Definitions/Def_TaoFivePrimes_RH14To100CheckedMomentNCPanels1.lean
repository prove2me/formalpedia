-- Prove2me | Definitions.Def_TaoFivePrimes_RH14To100CheckedMomentNCPanels1
-- name    : TaoFivePrimes_RH14To100CheckedMomentNCPanels1
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-22T09:50:16.613174+00:00
-- url     : https://prove2.me/theorems/23c44940-f42d-4a3b-b6a9-956886946f7f
-- title:
--   RH height 14–100 — certified moment data panels1
-- statement:
--   Four proposed moment-certificate data records, for panel indices 4 through 7. Each is constructed as a CheckedPanel with a kernel-checked Boolean validity field. The objects certify only the original finite arithmetic conditions; the analytic integral error bound is a separate theorem.
--
--   **Port note.** This is a port, to the Mathlib `777aaa6` / Lean v4.29.0-rc3 environment of the Riemann Hypothesis mission tree, of the definition `TaoFivePrimes_RH14To100CheckedMomentNCPanels1` (id `a06bf55e-3427-4ba0-ae53-3de5c8825ecc`, env `0df444a`, published by @raresbuhai). The Lean source is unchanged.
-- source:
--   sometik179, original height-14–100 certificate c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; original theta/Mellin foundations attributed to Gabewhigham. These same ordinary data and Boolean kernel validations occur in public moment-enclosure submission 821c0bfb-a758-4f7c-8bd3-e2b55ae05d26. The packet constructor validity proofs are necessary fields of dependent data structures; the substantive analytic enclosure remains a separate theorem.; ported from 0df444a definition a06bf55e-3427-4ba0-ae53-3de5c8825ecc

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
noncomputable def panel4 : CheckedPanel (4 : Fin 16) :=
  ⟨panelAt 4, sequenceCacheAt 4, by decide +kernel⟩
noncomputable def panel5 : CheckedPanel (5 : Fin 16) :=
  ⟨panelAt 5, sequenceCacheAt 5, by decide +kernel⟩
noncomputable def panel6 : CheckedPanel (6 : Fin 16) :=
  ⟨panelAt 6, sequenceCacheAt 6, by decide +kernel⟩
noncomputable def panel7 : CheckedPanel (7 : Fin 16) :=
  ⟨panelAt 7, sequenceCacheAt 7, by decide +kernel⟩
end RH14MomentCertificateData
def TaoFivePrimes_RH14To100CheckedMomentNCPanels1 : Nat := 14


