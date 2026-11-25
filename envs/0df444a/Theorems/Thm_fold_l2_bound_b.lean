-- Prove2me | Theorems.Thm_fold_l2_bound_b
-- name    : fold_l2_bound_b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:50.486053+00:00
-- url     : https://prove2.me/theorems/e7f4e39e-94ca-4433-850c-ac77d6301da5
-- title:
--   fold l2 bound b: fold l2 bound b
-- statement:
--   The fold l2 bound b construction uses the fold l2 bound b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesMemLp.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesMemLp.lean#L6-L7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PoincareSeriesMeasurability_FoldL2DoubleCoset
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PoincareSeriesMemLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem fold_l2_bound_b (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesMemLp G μ := by sorry
