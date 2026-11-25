-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_norm_lt_of_psi_ne
-- name    : ZetaZeros.D.EllReg.norm_lt_of_psi_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:47.71181+00:00
-- url     : https://prove2.me/theorems/a58c05a3-a615-523b-af6f-57ca53438252
-- title:
--   Ell Reg: norm lt of psi ne
-- statement:
--   The Ell Reg construction uses the norm lt of psi ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L39-L44

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section

theorem ZetaZeros.D.EllReg.norm_lt_of_psi_ne {d : ℕ} {ψ0 : E d → ℝ} (hψ0s : tsupport ψ0 ⊆ ball 0 2) {r : ℝ} (hr : 0 < r)
    {x x0 : E d} (hz : ψ0 (r⁻¹ • (x - x0)) ≠ 0) : ‖x - x0‖ < 2 * r := by sorry
