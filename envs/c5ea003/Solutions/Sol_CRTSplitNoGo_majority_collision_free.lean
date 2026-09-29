-- Prove2me | solution 1 for CRTSplitNoGo.majority_collision_free
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:46:59.403987+00:00
-- url     : https://prove2.me/submissions/9f3da8df-7b89-4633-a530-57f72c007df8

-- Sol generated from Bridges/CRTSplitNoGoBirthday.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Theorems.Thm_CRTSplitNoGo_card_injPrefix_ge

/-!
# The CRT-Split No-Go, Part VI: the birthday law for orbit prefixes

Parts I–V reduce the factor-revealing event of any `N`-explicit iteration to a cycle closure
of the reduced orbit mod `p`.  This file supplies the missing *quantitative* half for the
generic regime (a): an exact count of how many maps of a finite set have a collision-free
orbit prefix.

**Main theorem** (`card_injPrefix`).  Let `α` be a finite type with `n = card α` elements and
let `a : α`.  For `T < n`, the number of maps `f : α → α` whose orbit prefix
`a, f a, …, f^[T] a` is injective is exactly

  `(n - 1).descFactorial T * n ^ (n - T)`.

Equivalently, the fraction of maps with a collision-free prefix of length `T + 1` is
`∏_{i=1}^{T} (1 - i/n)`, the classical birthday product: it drops below `1/2` only once
`T ≍ √n`.  With `n = p ≈ √N` this is the `N^{1/4}` of Pollard rho, and it is exponential in
`log N`.

The proof is a fibration argument: the "reset" operation, which overwrites the value of `f`
at the last prefix point `f^[T] a`, has fibers of size exactly `n` inside the collision-free
set at level `T`, of which exactly `n - (T+1)` survive to level `T + 1`.  The key structural
input is `orb_eq_of_agree`: an orbit prefix depends only on the values of `f` at the earlier
prefix points, which is the finite-set shadow of Fact 2 (locality of iteration).

Small cases are cross-checked by exhaustive enumeration (`card_injPrefix_fin4_two`).
-/

open CRTSplitNoGo

variable {α : Type*} [Fintype α] [DecidableEq α]




















/-! ## The birthday bound: most maps are still collision-free at time `√n` -/






/-! ## Exhaustive cross-check of the birthday law on a small case

For `α = Fin 4`, `a = 0`, `T = 2` the law predicts `3 · 2 · 4² = 96` collision-free maps out of
`4⁴ = 256`.  The following is verified by kernel enumeration of all `256` maps. -/



open CRTSplitNoGo in
theorem solution(a : α) (T : ℕ) (hT : T < Fintype.card α)
    (h : T * (T + 1) ≤ Fintype.card α) :
    ((Fintype.card α : ℝ) ^ (Fintype.card α)) / 2 ≤ ((injPrefixFinset a T).card : ℝ) := by
  set n := Fintype.card α with hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hS : (T * (T + 1) : ℝ) / (2 * n) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : ((T * (T + 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ n := by positivity
  have := card_injPrefix_ge a T hT
  nlinarith [this]
