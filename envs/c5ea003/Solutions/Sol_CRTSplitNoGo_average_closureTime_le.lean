-- Prove2me | solution 1 for CRTSplitNoGo.average_closureTime_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:53:03.478929+00:00
-- url     : https://prove2.me/submissions/f9cf6f83-9c44-465d-960f-5b51c7b8d53f

-- Sol generated from Bridges/CRTSplitNoGoAverageUpper.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Theorems.Thm_CRTSplitNoGo_card_injPrefix_le_exp
import Theorems.Thm_CRTSplitNoGo_sum_closureTime_eq_sum_card
import Theorems.Thm_CRTSplitNoGo_sum_exp_birthday_le

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





open CRTSplitNoGo in
theorem solution(a : α) (hn : 0 < Fintype.card α) :
    ∑ f : α → α, (closureTime a f : ℝ)
      ≤ 3 * ((Nat.sqrt (Fintype.card α) : ℝ) + 1)
          * ((Fintype.card α : ℝ) ^ (Fintype.card α)) := by
  classical
  set n := Fintype.card α with hn'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlayer : ∑ f : α → α, (closureTime a f : ℝ)
      = ∑ T ∈ Finset.range n, ((injPrefixFinset a T).card : ℝ) := by
    have := sum_closureTime_eq_sum_card a
    have hcast : ((∑ f : α → α, closureTime a f : ℕ) : ℝ)
        = ((∑ T ∈ Finset.range n, (injPrefixFinset a T).card : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
    push_cast at hcast
    exact hcast
  have hbound : ∑ T ∈ Finset.range n, ((injPrefixFinset a T).card : ℝ)
      ≤ ∑ T ∈ Finset.range n,
          Real.exp (-((T * (T + 1) : ℝ) / (2 * n))) * (n : ℝ) ^ n := by
    refine Finset.sum_le_sum (fun T hT => ?_)
    exact card_injPrefix_le_exp a T (Finset.mem_range.mp hT)
  have hfactor : ∑ T ∈ Finset.range n,
      Real.exp (-((T * (T + 1) : ℝ) / (2 * n))) * (n : ℝ) ^ n
      = (∑ T ∈ Finset.range n, Real.exp (-((T * (T + 1) : ℝ) / (2 * n)))) * (n : ℝ) ^ n := by
    rw [← Finset.sum_mul]
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ n := by positivity
  calc ∑ f : α → α, (closureTime a f : ℝ)
      = ∑ T ∈ Finset.range n, ((injPrefixFinset a T).card : ℝ) := hlayer
    _ ≤ (∑ T ∈ Finset.range n, Real.exp (-((T * (T + 1) : ℝ) / (2 * n)))) * (n : ℝ) ^ n := by
        rw [← hfactor]; exact hbound
    _ ≤ (3 * ((Nat.sqrt n : ℝ) + 1)) * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (sum_exp_birthday_le n hn) hnn
