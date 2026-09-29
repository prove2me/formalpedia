-- Prove2me | Theorems.Thm_RainbowAP_spectrumThreshold_le
-- name    : RainbowAP.spectrumThreshold_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:12.609983+00:00
-- url     : https://prove2.me/theorems/f226ab83-5f63-4753-80eb-6a8ffb072a8b
-- title:
--   Upper bound: the full-spectrum threshold is at most `N log (2N) + 1`.
-- statement:
--   **Upper bound**: the full-spectrum threshold is at most `N log (2N) + 1`.
--
--   ```lean
--   theorem RainbowAP.spectrumThreshold_le(hN : 2 ≤ Fintype.card α) :
--       (spectrumThreshold α : ℝ)
--         ≤ (Fintype.card α : ℝ) * Real.log (2 * (Fintype.card α : ℝ)) + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumAsymptotics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumAsymptotics.lean#L125

-- Thm stub generated from Shared/RainbowAPSpectrumAsymptotics.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

/-!
# Asymptotics of the full-spectrum threshold

We turn the two arithmetic criteria of `Shared.RainbowAPSpectrumThreshold` into real analytic
bounds, showing that for an alphabet with `N ≥ 2` letters

  `(N - 1) * log (N + 1) ≤ spectrumThreshold α ≤ N * log (2 N) + 1`.

Both sides are `N log N (1 + o(1))`, so the threshold is asymptotically `N log N`.
-/

open Finset Real

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.spectrumThreshold_le(hN : 2 ≤ Fintype.card α) :
    (spectrumThreshold α : ℝ)
      ≤ (Fintype.card α : ℝ) * Real.log (2 * (Fintype.card α : ℝ)) + 1 := by sorry
