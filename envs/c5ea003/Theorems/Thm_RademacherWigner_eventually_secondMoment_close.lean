-- Prove2me | Theorems.Thm_RademacherWigner_eventually_secondMoment_close
-- name    : RademacherWigner.eventually_secondMoment_close
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:02:12.785639+00:00
-- url     : https://prove2.me/theorems/64f6f9c9-05b1-4173-b8d8-06c2fd0d716e
-- title:
--   Concentration at order two.
-- statement:
--   **Concentration at order two.**  For every `ε > 0`, eventually in `N` *all*
--   realisations of the ensemble have second spectral moment within `ε` of the
--   semicircle value; in particular the second moment converges in probability.
--
--   ```lean
--   theorem RademacherWigner.eventually_secondMoment_close(eps : ℝ) (heps : 0 < eps) :
--       ∀ᶠ N : ℕ in atTop, ∀ g : Config N,
--         |WignerBridge.normalizedMoment (W g) 2 - WignerSemicircle.semicircleMoment 2| < eps := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleLawLowOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleLawLowOrder.lean#L120

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

theorem RademacherWigner.eventually_secondMoment_close(eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop, ∀ g : Config N,
      |WignerBridge.normalizedMoment (W g) 2 - WignerSemicircle.semicircleMoment 2| < eps := by sorry
