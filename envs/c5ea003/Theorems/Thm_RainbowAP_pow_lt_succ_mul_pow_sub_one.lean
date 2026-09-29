-- Prove2me | Theorems.Thm_RainbowAP_pow_lt_succ_mul_pow_sub_one
-- name    : RainbowAP.pow_lt_succ_mul_pow_sub_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:11.665767+00:00
-- url     : https://prove2.me/theorems/ce692450-7e9c-4507-b34a-afbade577e06
-- title:
--   Pow lt succ mul pow sub one
-- statement:
--   Formal statement of `RainbowAP.pow_lt_succ_mul_pow_sub_one` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.pow_lt_succ_mul_pow_sub_one{N m : ℕ} (hN : 2 ≤ N)
--       (h : (m : ℝ) < ((N : ℝ) - 1) * Real.log ((N : ℝ) + 1)) :
--       N ^ m < (N + 1) * (N - 1) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumAsymptotics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumAsymptotics.lean#L21

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

theorem RainbowAP.pow_lt_succ_mul_pow_sub_one{N m : ℕ} (hN : 2 ≤ N)
    (h : (m : ℝ) < ((N : ℝ) - 1) * Real.log ((N : ℝ) + 1)) :
    N ^ m < (N + 1) * (N - 1) ^ m := by sorry
