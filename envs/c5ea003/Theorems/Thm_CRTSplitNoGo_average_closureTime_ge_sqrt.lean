-- Prove2me | Theorems.Thm_CRTSplitNoGo_average_closureTime_ge_sqrt
-- name    : CRTSplitNoGo.average_closureTime_ge_sqrt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:44.006072+00:00
-- url     : https://prove2.me/theorems/18a6eda2-e5a8-4d2c-b38a-d25b2a28cffc
-- title:
--   The average first closure time is at least `√n / 2`.
-- statement:
--   **The average first closure time is at least `√n / 2`.**  Specialising
--   `average_closureTime_ge` to `T + 1 = ⌊√n⌋`.
--
--   ```lean
--   theorem CRTSplitNoGo.average_closureTime_ge_sqrt(a : α) :
--       (Nat.sqrt (Fintype.card α) : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
--         ≤ ∑ f : α → α, (closureTime a f : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoAverage.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoAverage.lean#L106

-- Thm stub generated from Bridges/CRTSplitNoGoAverage.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail

/-!
# The CRT-Split No-Go, Part VIII: the average-case birthday barrier

Parts VI and VII count the maps whose orbit prefix is collision-free.  This file converts that
counting law into a statement about the *first closure time itself*, averaged over all maps —
the quantity that actually governs the running time of a rho-type factoring iteration.

For a map `f : α → α` and a seed `a`, `closureTime a f` is the least `T` at which the orbit
prefix `a, f a, …, f^[T] a` collides (it exists by pigeonhole, `not_injPrefix_card`).

**Main results.**

* `closureTime_spec` / `lt_closureTime_of_injPrefix` — `closureTime` is well defined and is a
  genuine first-collision time.
* `average_closureTime_ge` — for every `T` with `T (T+1) ≤ n = card α` the sum of the closure
  times over all `n ^ n` maps is at least `(T + 1) · n ^ n / 2`; equivalently, the *average*
  first closure time is at least `(T + 1)/2`.
* `average_closureTime_ge_sqrt` — taking `T + 1 = ⌊√n⌋` this gives an average first closure
  time of at least `√n / 2`: the birthday barrier holds on average, not merely with probability
  `1/2`.
* `average_closureTime_zmod` — on the reduced state space `ZMod p` of an `N`-explicit iteration
  (Fact 2), the average first closure time is at least `√p / 2`.  Since a factor of `N = p q`
  can be revealed only at a closure (Parts I–IV), a *typical* `N`-explicit iteration needs
  `≳ √p ≈ N^{1/4}/2` steps: exponential in `log N`.
-/

open CRTSplitNoGo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem CRTSplitNoGo.average_closureTime_ge_sqrt(a : α) :
    (Nat.sqrt (Fintype.card α) : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
      ≤ ∑ f : α → α, (closureTime a f : ℝ) := by sorry
