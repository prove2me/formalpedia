-- Prove2me | Theorems.Thm_fd_fj_near_sup
-- name    : fd_fj_near_sup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:52:10.488807+00:00
-- url     : https://prove2.me/theorems/0b917a55-2c0f-409c-84d8-94996b02bf26
-- title:
--   fd fj near sup: fd fj near sup
-- statement:
--   The fd fj near sup construction uses the fd fj near sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSup.lean#L3-L4
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSup.lean#L3-L4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_Inputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem fd_fj_near_sup {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] : ReciprocityTheory.ChartRestriction.G.FD.HolomorphicPeriodicityExtension (E := E) → ReciprocityTheory.ChartRestriction.G.FD.FlowNormRatio (E := E) → ReciprocityTheory.ChartRestriction.G.FD.ModerateCoefficientPositivity (E := E) → ReciprocityTheory.ChartRestriction.G.FD.NearSupremumTransference (E := E) := by sorry
