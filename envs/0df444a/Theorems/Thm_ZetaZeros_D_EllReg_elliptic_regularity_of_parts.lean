-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_elliptic_regularity_of_parts
-- name    : ZetaZeros.D.EllReg.elliptic_regularity_of_parts
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:26.936907+00:00
-- url     : https://prove2.me/theorems/3888e6f8-cce5-4914-91e5-5aec1059246d
-- title:
--   Ell Reg: elliptic regularity of parts
-- statement:
--   The Ell Reg construction uses the elliptic regularity of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegCheck.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllRegCheck.lean#L19-L24

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_SmoothOfLocallySmooth
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_IteratedPartialFourierChar
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingLocal
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Moments
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ConvolutionBound
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_SymbLower
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_PairingFourier
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeakFourier
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Decompose
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_ExistsSmoothExt
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_StepCore
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg

theorem ZetaZeros.D.EllReg.elliptic_regularity_of_parts : Internal := by sorry
