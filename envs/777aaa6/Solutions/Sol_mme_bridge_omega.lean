-- Prove2me | solution 1 for mme_bridge_omega
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-30T19:10:34.799277+00:00
-- url     : https://prove2.me/submissions/d4b4e5dc-1012-43f2-83b1-fde3646fe2be

import Definitions.Def_mme_tensor_bridge

/-! # Solution: bridge B — abstract `ωabs` ↔ Strassen-form `matMulExp_strassen K`.

Thin re-export of the assembled 75-line proof `MME.bridge_omega` in
`Def_mme_tensor_bridge`. That proof uses `mme_strassen_duality`, compactness of the
asymptotic spectrum, and the maximizing-point argument — all already on the platform
inside `Def_mme_duality` / `Def_mme_spectrum` / `Def_mme_mm_spectral`. -/

open MME

universe u

theorem solution {K : Type u} [Field K] :
    (mmTensorData K).omegaAbs = matMulExp_strassen K :=
  MME.bridge_omega
