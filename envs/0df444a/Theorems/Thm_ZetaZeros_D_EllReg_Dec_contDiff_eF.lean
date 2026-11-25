-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_Dec_contDiff_eF
-- name    : ZetaZeros.D.EllReg.Dec.contDiff_eF
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:09.387791+00:00
-- url     : https://prove2.me/theorems/c869db4c-78af-584f-bd34-e9212c838bec
-- title:
--   Dec: cont Diff e F
-- statement:
--   The Dec construction uses the cont Diff e F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L80-L83

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

theorem ZetaZeros.D.EllReg.Dec.contDiff_eF (ξ : E d) : ContDiff ℝ ∞ (eF ξ) := by sorry
