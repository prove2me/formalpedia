-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_frozenKernelSmall
-- name    : ZetaZeros.D.EllReg.frozenKernelSmall
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:17.768749+00:00
-- url     : https://prove2.me/theorems/f56a6fe3-02db-44e5-9326-66388782a71e
-- title:
--   Ell Reg: frozen Kernel Small
-- statement:
--   The Ell Reg construction uses the frozen Kernel Small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L46-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/ExistsSmoothExt.lean#L46-L120

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDil
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDer
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt
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

theorem ZetaZeros.D.EllReg.frozenKernelSmall : KernelSmall := by sorry
