-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_om_nonneg
-- name    : ZetaZeros.D.EllReg.om_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:13:56.102855+00:00
-- url     : https://prove2.me/theorems/001981b7-b1bc-41f5-bc84-d8761b7edd1d
-- title:
--   Ell Reg: om nonneg
-- statement:
--   The Ell Reg construction uses the om nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeightedNormFinite.lean#L9-L12

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

theorem ZetaZeros.D.EllReg.om_nonneg {d : ℕ} (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by sorry
