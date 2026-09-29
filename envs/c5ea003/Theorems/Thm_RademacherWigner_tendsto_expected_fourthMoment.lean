-- Prove2me | Theorems.Thm_RademacherWigner_tendsto_expected_fourthMoment
-- name    : RademacherWigner.tendsto_expected_fourthMoment
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:05:31.290062+00:00
-- url     : https://prove2.me/theorems/07c34c8b-7cab-4191-ad23-5709464f24bc
-- title:
--   Semicircle law, order four (in expectation).
-- statement:
--   **Semicircle law, order four (in expectation).**  The expected fourth moment of
--   the empirical spectral distribution of `W/√N` converges to the fourth moment
--   `C₂ = 2` of the semicircle law.
--
--   ```lean
--   theorem RademacherWigner.tendsto_expected_fourthMoment:
--       Tendsto (fun N : ℕ => expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4))
--         atTop (𝓝 (WignerSemicircle.semicircleMoment 4)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleLawLowOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleLawLowOrder.lean#L97

-- Thm stub generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The semicircle law at orders two and four for the Rademacher Wigner ensemble

Combining

* `Probability.WignerSemicircleMoments` (moments of the semicircle law are Catalan
  numbers),
* `Probability.WignerTraceBridge` (empirical spectral moments = normalised traces),
* `Probability.WignerRademacherEnsemble` (exact trace moments of the ensemble),

this file proves the moment-method form of the Wigner semicircle law at the first
two nontrivial orders:

* `esd_secondMoment` : the second moment of the empirical spectral distribution of
  `W/√N` equals `1 - 1/N` for **every** realisation (perfect self-averaging), and
  converges to `∫ x² dsc(x) = C₁ = 1`;
* `expect_normalizedMoment_four` : the expected fourth moment equals
  `(N-1)(2N-3)/N²`, converging to `∫ x⁴ dsc(x) = C₂ = 2`;
* `eventually_secondMoment_close` : a (deterministic, hence in-probability)
  concentration statement for the second moment.
-/

open Matrix BigOperators Filter Topology

open RademacherWigner

variable {N : ℕ}







/-! ### Convergence to the semicircle moments -/

theorem RademacherWigner.tendsto_expected_fourthMoment:
    Tendsto (fun N : ℕ => expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4))
      atTop (𝓝 (WignerSemicircle.semicircleMoment 4)) := by sorry
