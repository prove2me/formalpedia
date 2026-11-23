-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_WF_ev_cons
-- name    : ZetaZeros.D.EllReg.WF.ev_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:18.660809+00:00
-- url     : https://prove2.me/theorems/b5c1c95b-3d26-40bb-9dfb-d623a352c3f1
-- title:
--   WF: ev cons
-- statement:
--   The WF construction uses the ev cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/WeakFourier.lean#L78-L80

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

theorem ZetaZeros.D.EllReg.WF.ev_cons (p : List (Fin d) × (E d → ℂ)) (L : List (List (Fin d) × (E d → ℂ))) (g : E d → ℂ) (y : E d) :
    ev (p :: L) g y = p.2 y * dw p.1 g y + ev L g y := by sorry
