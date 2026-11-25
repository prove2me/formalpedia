-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_om_sq_le
-- name    : ZetaZeros.D.EllReg.om_sq_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:21.417019+00:00
-- url     : https://prove2.me/theorems/716c6df5-b01b-4c89-8f28-71c0aab7fe6c
-- title:
--   Ell Reg: om sq le
-- statement:
--   The Ell Reg construction uses the om sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L120-L123

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
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

theorem ZetaZeros.D.EllReg.om_sq_le {d : ℕ} (s M ε : ℝ) (hε : 0 < ε) (ξ : E d) :
    om s M ε ξ ^ 2 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) := by sorry
