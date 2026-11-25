-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_tsupport_cut
-- name    : ZetaZeros.D.EllReg.Dec.tsupport_cut
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:23:03.604289+00:00
-- url     : https://prove2.me/theorems/01d39aa9-b2e6-4fb7-aa9b-1e22381f1f3c
-- title:
--   Dec: tsupport cut
-- statement:
--   The Dec construction uses the tsupport cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L118-L119

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
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
open ZetaZeros.D.EllReg.Dec
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.Dec.tsupport_cut (χ : E d → ℝ) (u : E d → ℂ) : tsupport (cut χ u) ⊆ tsupport χ := by sorry
