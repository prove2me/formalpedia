-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_cutoffContinuous
-- name    : ZetaZeros.D.EllReg.cutoffContinuous
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:30.634192+00:00
-- url     : https://prove2.me/theorems/97608a08-3351-550b-993e-cb894b849895
-- title:
--   Ell Reg: cutoff Continuous
-- statement:
--   The Ell Reg construction uses the cutoff Continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/SmoothOfLocallySmooth.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/SmoothOfLocallySmooth.lean#L29-L41

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_SmoothOfLocallySmooth
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

theorem ZetaZeros.D.EllReg.cutoffContinuous : CutCont := by sorry
