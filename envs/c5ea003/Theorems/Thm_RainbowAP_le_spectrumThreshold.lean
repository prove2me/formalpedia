-- Prove2me | Theorems.Thm_RainbowAP_le_spectrumThreshold
-- name    : RainbowAP.le_spectrumThreshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:48:54.284651+00:00
-- url     : https://prove2.me/theorems/68b1351b-ed39-4068-a9db-b05be9d5cf16
-- title:
--   Lower bound: the full-spectrum threshold is at least `(N - 1) log (N + 1)`.
-- statement:
--   **Lower bound**: the full-spectrum threshold is at least `(N - 1) log (N + 1)`.
--
--   ```lean
--   theorem RainbowAP.le_spectrumThreshold(hN : 2 ≤ Fintype.card α) :
--       ((Fintype.card α : ℝ) - 1) * Real.log ((Fintype.card α : ℝ) + 1)
--         ≤ (spectrumThreshold α : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumAsymptotics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumAsymptotics.lean#L149

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

theorem RainbowAP.le_spectrumThreshold(hN : 2 ≤ Fintype.card α) :
    ((Fintype.card α : ℝ) - 1) * Real.log ((Fintype.card α : ℝ) + 1)
      ≤ (spectrumThreshold α : ℝ) := by sorry
