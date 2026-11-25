-- Prove2me | Theorems.Thm_quotient_sigma_finite
-- name    : quotient_sigma_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:07.532198+00:00
-- url     : https://prove2.me/theorems/14d3e0d8-1332-4381-bf09-890fc5502406
-- title:
--   quotient sigma finite: quotient sigma finite
-- statement:
--   The quotient sigma finite construction uses the quotient sigma finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QuotNuSigma.lean#L4-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QuotNuSigma.lean#L4-L6

import Definitions.Def_Formalism_PeriodIntegrals_QuotNuSigma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientSigmaFiniteness_SigmaFiniteOfWeil
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QuotNuSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem quotient_sigma_finite : PI.QuotNuSigma.Target := by sorry
