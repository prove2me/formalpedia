-- Prove2me | Theorems.Thm_isLattice_of_discriminant
-- name    : isLattice_of_discriminant
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:44.849811+00:00
-- url     : https://prove2.me/theorems/7afda6f4-ce34-4978-8c2a-63a171b0ecee
-- title:
--   is Lattice of discriminant: is Lattice of discriminant
-- statement:
--   The is Lattice of discriminant construction uses the is Lattice of discriminant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantTheorems/TBDisc.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantTheorems/TBDisc.lean#L9-L10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBDisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem isLattice_of_discriminant : ReciprocityTheory.ChartRestriction.G.TB.IsLatticeOfDiscSt := by sorry
