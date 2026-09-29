-- Prove2me | Definitions.Def_Bridges_CRTSplitNoGoAverage
-- name    : Bridges_CRTSplitNoGoAverage
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:52.10095+00:00
-- url     : https://prove2.me/theorems/f72ed6c6-0213-4197-8664-9ffd2396823a
-- title:
--   Aether Catalog definitions — Bridges_CRTSplitNoGoAverage
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CRTSplitNoGoAverage`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CRTSplitNoGoAverage.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
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

namespace CRTSplitNoGo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]



/-- The first time at which the orbit prefix from `a` collides. -/
noncomputable def closureTime (a : α) (f : α → α) : ℕ :=
  sInf {T : ℕ | ¬ InjPrefix f a T}







end CRTSplitNoGo


