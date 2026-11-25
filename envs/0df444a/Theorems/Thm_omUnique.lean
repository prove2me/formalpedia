-- Prove2me | Theorems.Thm_omUnique
-- name    : omUnique
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:06:38.026776+00:00
-- url     : https://prove2.me/theorems/956b4ce6-a7a3-4cdf-a995-81514d6e067e
-- title:
--   om Unique: om Unique
-- statement:
--   The om Unique construction uses the om Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/OmFibreUniq.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/OmFibreUniq.lean#L9-L14

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OmFibreUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_GramMapFibreUniqueness
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExInst
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_OmFibreUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

theorem omUnique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (a : ℕ) :
    PI.OmFibreUniq.OmUnique σ J ψ v a := by sorry
