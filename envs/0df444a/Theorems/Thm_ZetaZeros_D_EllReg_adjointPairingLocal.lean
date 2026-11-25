-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_adjointPairingLocal
-- name    : ZetaZeros.D.EllReg.adjointPairingLocal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:42.210993+00:00
-- url     : https://prove2.me/theorems/2d4dfb8e-601e-4e2b-850c-817b15657dd6
-- title:
--   Ell Reg: adjoint Pairing Local
-- statement:
--   The Ell Reg construction uses the adjoint Pairing Local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingLocal.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/PairingLocal.lean#L17-L35

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingLocal
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

theorem ZetaZeros.D.EllReg.adjointPairingLocal : PairingLocal := by sorry
