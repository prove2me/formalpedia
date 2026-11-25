-- Prove2me | Theorems.Thm_ZetaZeros_D_EllReg_frozenDecompositionOfParts
-- name    : ZetaZeros.D.EllReg.frozenDecompositionOfParts
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:11.213181+00:00
-- url     : https://prove2.me/theorems/64e9b52f-1eb0-41fa-b737-3e105a3d8c1c
-- title:
--   Ell Reg: frozen Decomposition Of Parts
-- statement:
--   The Ell Reg construction uses the frozen Decomposition Of Parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L170-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/EllipticRegularity/Decompose.lean#L170-L272

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

theorem ZetaZeros.D.EllReg.frozenDecompositionOfParts : DecomposeOf := by sorry
