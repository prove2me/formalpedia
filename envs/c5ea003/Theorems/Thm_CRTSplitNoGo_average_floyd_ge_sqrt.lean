-- Prove2me | Theorems.Thm_CRTSplitNoGo_average_floyd_ge_sqrt
-- name    : CRTSplitNoGo.average_floyd_ge_sqrt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:59.107783+00:00
-- url     : https://prove2.me/theorems/8c97a234-152b-4f2d-bd20-fa0220e63836
-- title:
--   The average-case barrier for Pollard rho itself.
-- statement:
--   **The average-case barrier for Pollard rho itself.**  Let `ftime` assign to every map a
--   tortoise-and-hare match time (any `i > 0` with `f^[i] a = f^[2i] a` — in particular the first
--   such `i`, which is what the Pollard rho loop returns).  Then the average of `ftime` over all
--   `n ^ n` maps is at least `⌊√n⌋ / 4`.  Cycle detection cannot beat the birthday exponent even by
--   using the hare.
--
--   ```lean
--   theorem CRTSplitNoGo.average_floyd_ge_sqrt(a : α) (ftime : (α → α) → ℕ)
--       (hpos : ∀ f, 0 < ftime f)
--       (hmatch : ∀ f, orb f a (ftime f) = orb f a (2 * ftime f)) :
--       (Nat.sqrt (Fintype.card α) : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 4)
--         ≤ ∑ f : α → α, (ftime f : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoAverageUpper.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoAverageUpper.lean#L288

-- Thm stub generated from Bridges/CRTSplitNoGoAverageUpper.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage
import Definitions.Def_Bridges_CRTSplitNoGoBirthday

/-!
# The CRT-Split No-Go, Part IX: the average closure time is `Θ(√n)`, and Floyd inherits it

Part VIII proved the *lower* half of the average-case barrier: averaged over all `n ^ n` maps of
an `n`-element set, the first orbit collision happens no earlier than `⌊√n⌋ / 2` steps.  This
file closes the matching *upper* half — Conjecture E of the previous cycle's
`FUTURE_DIRECTIONS.md` — and transfers both halves to the tortoise-and-hare (Floyd) test that
Pollard rho actually runs.

## Main results

* `sum_closureTime_eq_sum_card` — the layer-cake identity
  `∑_f closureTime a f = ∑_{T < n} #{f : collision-free prefix of length T+1}`.
  It is exact: closure times and the birthday counting law of Part VI are the same data.
* `sum_exp_birthday_le` — the analytic core: `∑_{T < n} exp (−T(T+1)/(2n)) ≤ 3 (⌊√n⌋ + 1)`,
  proved by cutting `[0, n)` into `⌊√n⌋ + 1` blocks on which the Gaussian tail of Part VII is
  dominated by the geometric ratio `exp (−1/2)`.
* `average_closureTime_le` — consequently `∑_f closureTime a f ≤ 3 (⌊√n⌋ + 1) · n ^ n`: the
  average first closure time is `O(√n)`.  With `average_closureTime_ge_sqrt` this pins the
  average at `Θ(√n)`, recorded as `average_closureTime_theta` and, on the reduced state space
  of an `N`-explicit iteration, as `average_closureTime_theta_zmod`.
* `closureTime_le_two_mul_floyd` — a tortoise-and-hare match at time `i > 0` forces a collision
  in the prefix of length `2i + 1`, so Floyd's detection time is at least half the first closure
  time; `average_floyd_ge_sqrt` and `average_floyd_zmod` therefore give the `√p / 4` average
  lower bound for the actual Pollard rho loop, not merely for the idealised first closure.

Together with Parts I–IV (a factor of `N = p q` appears *exactly* at an exclusive mod-`p`
closure) this says: on the reduced state space `ZMod p` the generic regime costs `Θ(√p)` on
average — `N^{1/4}` for balanced `N`, exponential in `log N` — and no rho-type variant, Floyd
included, can do better than a constant factor.
-/

open CRTSplitNoGo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Part A: closure times are the layer cake of the birthday counts -/




/-! ## Part B: the analytic core — summing the Gaussian tail -/






/-! ## Part C: the average closure time is `Θ(√n)` -/




/-! ## Part D: the tortoise-and-hare test inherits the barrier -/

theorem CRTSplitNoGo.average_floyd_ge_sqrt(a : α) (ftime : (α → α) → ℕ)
    (hpos : ∀ f, 0 < ftime f)
    (hmatch : ∀ f, orb f a (ftime f) = orb f a (2 * ftime f)) :
    (Nat.sqrt (Fintype.card α) : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 4)
      ≤ ∑ f : α → α, (ftime f : ℝ) := by sorry
