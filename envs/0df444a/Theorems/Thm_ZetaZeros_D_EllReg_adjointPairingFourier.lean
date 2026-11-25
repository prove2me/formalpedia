-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_adjointPairingFourier
-- name    : ZetaZeros.D.EllReg.adjointPairingFourier
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:38.795844+00:00
-- url     : https://prove2.me/theorems/bcaaf5b7-4ebd-4c15-b24a-1bda4d462d91
-- title:
--   Ell Reg: adjoint Pairing Fourier
-- statement:
--   The Ell Reg construction uses the adjoint Pairing Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L201-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingFourier.lean#L201-L249

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

theorem ZetaZeros.D.EllReg.adjointPairingFourier : PairingFourier := by sorry
