-- Prove2me | Theorems.Thm_g_lattice_hermitian
-- name    : g_lattice_hermitian
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:39.13757+00:00
-- url     : https://prove2.me/theorems/5ce2e29b-6f81-4d04-932e-27426c1cdacc
-- title:
--   g lattice hermitian: g lattice hermitian
-- statement:
--   The g lattice hermitian construction uses the g lattice hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DvGLatHerm.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DvGLatHerm.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvGLatHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem g_lattice_hermitian : PI.Dv.GLatHerm := by sorry
