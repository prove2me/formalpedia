-- Prove2me | Theorems.Thm_kernel_lattice_t0_exists
-- name    : kernel_lattice_t0_exists
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:07:51.616837+00:00
-- url     : https://prove2.me/theorems/2cecf374-a159-50aa-8b73-0f91333c4f52
-- title:
--   kernel lattice t0 exists: kernel lattice t0 exists
-- statement:
--   The kernel lattice t0 exists construction uses the kernel lattice t0 exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KernelLatticeT0Exists.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KernelLatticeT0Exists.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerCoordinatesZero_IntCoordsZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KernelLatticeT0Exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem kernel_lattice_t0_exists : PI.KerLat.ExistsTwoTorsionOffKernels := by sorry
