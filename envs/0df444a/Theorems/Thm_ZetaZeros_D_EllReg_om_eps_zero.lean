-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_om_eps_zero
-- name    : ZetaZeros.D.EllReg.om_eps_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:42.993251+00:00
-- url     : https://prove2.me/theorems/0b28e2cc-e58a-4cb8-a127-bd197d13fff1
-- title:
--   Ell Reg: om eps zero
-- statement:
--   The Ell Reg construction uses the om eps zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L20-L22

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

theorem ZetaZeros.D.EllReg.om_eps_zero {d : ℕ} (s M : ℝ) (ξ : E d) : om s M 0 ξ = om s 0 0 ξ := by sorry
