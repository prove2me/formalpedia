-- Prove2me | Theorems.Thm_RainbowAP_two_mul_pow_lt_pow
-- name    : RainbowAP.two_mul_pow_lt_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:18.692333+00:00
-- url     : https://prove2.me/theorems/231f8b03-be9d-4b3b-aebc-bb87ebbb4926
-- title:
--   Two mul pow lt pow
-- statement:
--   Formal statement of `RainbowAP.two_mul_pow_lt_pow` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.two_mul_pow_lt_pow{N m : ℕ} (hN : 2 ≤ N)
--       (h : (N : ℝ) * Real.log (2 * (N : ℝ)) < m) :
--       2 * N * (N - 1) ^ m < N ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumAsymptotics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumAsymptotics.lean#L66

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

theorem RainbowAP.two_mul_pow_lt_pow{N m : ℕ} (hN : 2 ≤ N)
    (h : (N : ℝ) * Real.log (2 * (N : ℝ)) < m) :
    2 * N * (N - 1) ^ m < N ^ m := by sorry
