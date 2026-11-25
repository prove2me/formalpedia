-- Prove2me | Theorems.Thm_fd_point_assembly
-- name    : fd_point_assembly
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:07.030424+00:00
-- url     : https://prove2.me/theorems/dfc5e44f-efb7-5d1a-bb0a-88a1b0d4d656
-- title:
--   fd point assembly: fd point assembly
-- statement:
--   The fd point assembly construction uses the fd point assembly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/FdPointAssembly.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/PointAssembly/FdPointAssembly.lean#L6-L9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FourierJacobiDifferentiable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_FdPointAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open PIW.FdPA

theorem fd_point_assembly {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.ShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalFlagTranslate (E := E) → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartNormControl (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) → ReciprocityTheory.ChartRestriction.G.FD.SchwarzLemmaBall → ReciprocityTheory.ChartRestriction.G.FD.OrthonormalShortVectorBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.IsotropicCoefficientSplitting (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NoShortVectorLowerBound (E := E) → ReciprocityTheory.ChartRestriction.G.FD.UnitaryUnipotentMove (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainPointBound (E := E) := by sorry
