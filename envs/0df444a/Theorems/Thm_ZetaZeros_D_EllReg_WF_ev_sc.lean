-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_sc
-- name    : ZetaZeros.D.EllReg.WF.ev_sc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:13:22.582079+00:00
-- url     : https://prove2.me/theorems/cbd46749-64b9-48e3-a575-b043c574dd03
-- title:
--   WF: ev sc
-- statement:
--   The WF construction uses the ev sc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L92-L100

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
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
open ZetaZeros.D.EllReg.WF
variable {d : ℕ}

theorem ZetaZeros.D.EllReg.WF.ev_sc (C : E d → ℂ) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (sc C L) g y = C y * ev L g y := by sorry
