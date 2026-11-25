-- Prove2me | Theorems.Thm_poincareSeries_finite
-- name    : poincareSeries_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:15:54.692889+00:00
-- url     : https://prove2.me/theorems/4edb1272-10e6-4f08-93ac-75fcf06b53be
-- title:
--   poincare Series finite: poincare Series finite
-- statement:
--   The poincare Series finite construction uses the poincare Series finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesFinite.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesFinite.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuotientIntegralBound_QuotientLIntegralLeMultiplicityLIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PoincareSeriesFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ := by sorry
