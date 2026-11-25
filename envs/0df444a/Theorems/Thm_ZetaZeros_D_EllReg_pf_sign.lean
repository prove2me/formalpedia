-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_pf_sign
-- name    : ZetaZeros.D.EllReg.pf_sign
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:38.144223+00:00
-- url     : https://prove2.me/theorems/fa5a80a8-cb22-5571-8e31-c0ec4ff04050
-- title:
--   Ell Reg: pf sign
-- statement:
--   The Ell Reg construction uses the pf sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L190-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L190-L199

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
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
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.pf_sign (n : ℕ) (w : Fin n → Fin d) (η : E d) :
    (-1 : ℂ) ^ n * ∏ l, (2 * Real.pi * Complex.I * (((-η) (w l) : ℝ) : ℂ)) = mono w η := by sorry
