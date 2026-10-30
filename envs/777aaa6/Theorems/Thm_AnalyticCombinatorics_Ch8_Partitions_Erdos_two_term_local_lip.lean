-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_two_term_local_lip
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.two_term_local_lip
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:09:48.006522+00:00
-- url     : https://prove2.me/theorems/b250c839-4730-43d5-a25b-88f17a946ce7
-- title:
--   A local Lipschitz estimate from a uniform two-term expansion
-- statement:
--   A bridge conditional on the full uniform two-term expansion of an arbitrary function; it neither assumes away nor itself proves the concrete moment expansion.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem two_term_local_lip (f : ℕ → ℝ) (c₀ c₁ K W0 : ℝ) (hK : 0 ≤ K) (hW0 : 0 ≤ W0)
--       (hexp : ∀ᶠ n : ℕ in atTop, |f n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ)) :
--       ∃ K' R0 : ℝ, 0 < K' ∧ ∀ x y : ℕ, R0 ≤ (x : ℝ) → R0 ≤ (y : ℝ) →
--         |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| ≤ W0 → |f x - f y| ≤ K' / (x : ℝ)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TwoTermLocalLip.lean#L22. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: two-term expansion ⟹ local Lipschitz (η ~ 1/r²)

⚠ DRAFT — written WITHOUT a local build (server down); queued for batch verification on uisai1 recovery.

Modular bridge from the smooth-rank mean-decrement two-term expansion `f n = c₀ + c₁/√n + O(1/n)` to the
approximate-martingale bound `|f x − f y| ≤ K'/x` for comparable starts (`|√x − √y| ≤ W0`).  The constant
`c₀` cancels; `|c₁/√x − c₁/√y| = O(W0/x)` (since `√x√y ≥ x/2` for large `x`); the two `O(1/n)` remainders
are `O(1/x)` (since `y ≥ x/4`).  Hence `|f x − f y| ≤ (5K + 2|c₁|W0)/x = O(1/r²)`, `r = 3√x`.  Consumes the
(still-to-prove) two-term Lambert-moment expansion as a hypothesis.  Opus-authored.
-/

open Filter Topology

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.two_term_local_lip (f : ℕ → ℝ) (c₀ c₁ K W0 : ℝ) (hK : 0 ≤ K) (hW0 : 0 ≤ W0)
    (hexp : ∀ᶠ n : ℕ in atTop, |f n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ)) :
    ∃ K' R0 : ℝ, 0 < K' ∧ ∀ x y : ℕ, R0 ≤ (x : ℝ) → R0 ≤ (y : ℝ) →
      |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| ≤ W0 → |f x - f y| ≤ K' / (x : ℝ) := by sorry
