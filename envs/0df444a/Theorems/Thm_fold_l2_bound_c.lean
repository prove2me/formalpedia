-- Prove2me | Theorems.Thm_fold_l2_bound_c
-- name    : fold_l2_bound_c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:48.696067+00:00
-- url     : https://prove2.me/theorems/731a106b-ab2f-4b0a-a168-3f40b574eacf
-- title:
--   fold l2 bound c: fold l2 bound c
-- statement:
--   The fold l2 bound c construction uses the fold l2 bound c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesInner.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PoincareSeriesInner.lean#L6-L7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_FoldL2ComplexOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PoincareSeriesInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem fold_l2_bound_c (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesInner G μ := by sorry
