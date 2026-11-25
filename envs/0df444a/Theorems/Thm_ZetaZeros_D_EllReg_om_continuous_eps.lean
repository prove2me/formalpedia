-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_om_continuous_eps
-- name    : ZetaZeros.D.EllReg.om_continuous_eps
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:56.065828+00:00
-- url     : https://prove2.me/theorems/5de74c36-6264-48b6-9ed2-4560e3be2c75
-- title:
--   Ell Reg: om continuous eps
-- statement:
--   The Ell Reg construction uses the om continuous eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L14-L18

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

theorem ZetaZeros.D.EllReg.om_continuous_eps {d : ℕ} (s M : ℝ) (ξ : E d) : Continuous fun ε : ℝ => om s M ε ξ := by sorry
