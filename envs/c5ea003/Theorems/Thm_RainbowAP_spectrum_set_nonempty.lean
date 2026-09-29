-- Prove2me | Theorems.Thm_RainbowAP_spectrum_set_nonempty
-- name    : RainbowAP.spectrum_set_nonempty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:17.589202+00:00
-- url     : https://prove2.me/theorems/0b0c6604-619d-42c0-862a-99712313a49e
-- title:
--   Spectrum set nonempty
-- statement:
--   Formal statement of `RainbowAP.spectrum_set_nonempty` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.spectrum_set_nonempty(hN : 2 ≤ Fintype.card α) :
--       {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumAsymptotics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumAsymptotics.lean#L114

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

theorem RainbowAP.spectrum_set_nonempty(hN : 2 ≤ Fintype.card α) :
    {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty := by sorry
