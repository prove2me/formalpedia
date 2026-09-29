-- Prove2me | Theorems.Thm_RainbowAP_lt_T_of
-- name    : RainbowAP.lt_T_of
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:27:26.372201+00:00
-- url     : https://prove2.me/theorems/555e3e5e-3c77-4538-a584-458d5113c313
-- title:
--   Lt of
-- statement:
--   Formal statement of `RainbowAP.lt_T_of` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.lt_T_of{k m : ℕ} (hk : 2 ≤ k)
--       (h : (k ^ 2) ^ m < (k ^ 2 + 1) * (k ^ 2 - 1) ^ m) : m < T k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSmallCases.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSmallCases.lean#L25

-- Thm stub generated from Shared/RainbowAPSmallCases.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPPairThreshold

/-!
# Verified small cases of the rainbow pair-spectrum threshold

Combining the two majority criteria with the monotonicity of the transition
(`RainbowAP.majority_iff_threshold_le`) pins `T k` inside an explicit integer window for each
small `k`.  These windows are computed here by pure numeral arithmetic; they agree with the exact
values `T 2 = 7`, `T 3 = 23`, `T 4 = 51` obtained by inclusion–exclusion outside Lean
(see `ComputationalEvidence.md`).
-/

open RainbowAP

theorem RainbowAP.lt_T_of{k m : ℕ} (hk : 2 ≤ k)
    (h : (k ^ 2) ^ m < (k ^ 2 + 1) * (k ^ 2 - 1) ^ m) : m < T k := by sorry
