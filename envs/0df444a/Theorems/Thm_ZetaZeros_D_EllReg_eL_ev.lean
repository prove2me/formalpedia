-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_eL_ev
-- name    : ZetaZeros.D.EllReg.eL_ev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:04.372803+00:00
-- url     : https://prove2.me/theorems/1aae7bd0-f9d0-40c6-8343-481b9a0fe434
-- title:
--   Ell Reg: e L ev
-- statement:
--   The Ell Reg construction uses the e L ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/IteratedPartialFourierChar.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/IteratedPartialFourierChar.lean#L22-L25

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
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

theorem ZetaZeros.D.EllReg.eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by sorry
