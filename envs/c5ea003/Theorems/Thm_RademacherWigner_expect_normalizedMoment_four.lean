-- Prove2me | Theorems.Thm_RademacherWigner_expect_normalizedMoment_four
-- name    : RademacherWigner.expect_normalizedMoment_four
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:04:17.039686+00:00
-- url     : https://prove2.me/theorems/44d1e03c-f7f6-4022-8f46-420184f50c36
-- title:
--   Expected normalised fourth spectral moment of the Rademacher Wigner
-- statement:
--   **Expected normalised fourth spectral moment** of the Rademacher Wigner
--   ensemble: exactly `(N-1)(2N-3)/N²`.
--
--   ```lean
--   theorem RademacherWigner.expect_normalizedMoment_four(N : ℕ) (hN : 0 < N) :
--       expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4) =
--         ((N : ℝ) - 1) * (2 * (N : ℝ) - 3) / (N : ℝ) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleLawLowOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleLawLowOrder.lean#L61

-- Thm stub generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
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

theorem RademacherWigner.expect_normalizedMoment_four(N : ℕ) (hN : 0 < N) :
    expect (fun g : Config N => WignerBridge.normalizedMoment (W g) 4) =
      ((N : ℝ) - 1) * (2 * (N : ℝ) - 3) / (N : ℝ) ^ 2 := by sorry
