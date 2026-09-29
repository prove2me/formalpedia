-- Prove2me | Theorems.Thm_RademacherWigner_esd_secondMoment
-- name    : RademacherWigner.esd_secondMoment
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-15T02:47:33.562191+00:00
-- url     : https://prove2.me/theorems/5758a910-1655-48a1-b23f-2c07ff0086a3
-- title:
--   Spelled out at the level of eigenvalues: the empirical spectral distribution of
-- statement:
--   Spelled out at the level of eigenvalues: the empirical spectral distribution of
--   `W/√N` has second moment exactly `1 - 1/N`.
--
--   ```lean
--   theorem RademacherWigner.esd_secondMoment(g : Config N) (hN : 0 < N) :
--       (1 / (N : ℝ)) *
--           ∑ i, ((W_isHermitian g).eigenvalues i / Real.sqrt (N : ℝ)) ^ 2 = 1 - 1 / (N : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleLawLowOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleLawLowOrder.lean#L46

-- Thm stub generated from Probability/WignerSemicircleLawLowOrder.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Theorems.Thm_RademacherWigner_W_isHermitian
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

theorem RademacherWigner.esd_secondMoment(g : Config N) (hN : 0 < N) :
    (1 / (N : ℝ)) *
        ∑ i, ((W_isHermitian g).eigenvalues i / Real.sqrt (N : ℝ)) ^ 2 = 1 - 1 / (N : ℝ) := by sorry
