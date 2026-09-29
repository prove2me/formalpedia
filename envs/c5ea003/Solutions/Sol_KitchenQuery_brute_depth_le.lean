-- Prove2me | solution 1 for KitchenQuery.brute_depth_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T08:15:24.259832+00:00
-- url     : https://prove2.me/submissions/906142d0-816d-47fd-a137-2dbe2c7103dd

/-
# `KitchenQuery.brute_depth_le`
Target `7448403c` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle screened CLEAN (exit 0). Gift check with the corrected logic: **SAFE**.

BINDERS — no WA (history is CE,CE,CE,CE), so no published expected type. The statement declares its
arguments INLINE — `(f : Dish n) (k : ℕ) (a : Pantry n)` — and the only section-inherited binder is
`variable {n : ℕ}` (bundle line 85, outside `namespace Taste`). The generated gate is the authority
and fails closed on mismatch.

MATHS. The bundle retains the definition:

    def brute (f : Dish n) : ℕ → Pantry n → Taste n
      | 0,     a => .serve (f a)
      | (k+1), a => if h : k < n then
                      .probe ⟨k,h⟩ (brute f k (Function.update a ⟨k,h⟩ false))
                                   (brute f k (Function.update a ⟨k,h⟩ true))
                    else brute f k a

Induction on `k`, **generalizing `a`** — this is the crux. Each recursive call is made at a DIFFERENT
pantry (`Function.update a ...`), so an inductive hypothesis fixed at one `a` would be useless.

  * `k = 0` — the strategy serves immediately, depth `0`.
  * `k+1`, probe branch — depth is `1 + max` of the two branch depths; both branches are `brute f k`
    at updated pantries, so both are `≤ k` by the generalized IH, hence the max is `≤ k` and the
    whole is `≤ k+1`.
  * `k+1`, skip branch (`¬ k < n`) — the strategy is literally `brute f k a`, so `≤ k ≤ k+1`.

PROBED, NOT GUESSED:
  * `max_le : a ≤ c → b ≤ c → max a b ≤ c` — needed BEFORE any arithmetic, since `max` is not linear
    and `omega` cannot see through it. This is the same obstacle anticipated in `b16b10b5`.
  * `Nat.le_succ`.
-/
import Mathlib
import Definitions.Def_Novelty_KitchenQueryComplexity

set_option autoImplicit false
set_option maxHeartbeats 400000

open KitchenQuery


open KitchenQuery in
/-- **The target, verbatim.** -/
theorem solution {n : ℕ} (f : Dish n) (k : ℕ) (a : Pantry n) :
    (brute f k a).depth ≤ k := by
  induction k generalizing a with
  | zero => simp [brute, Taste.depth]
  | succ k ih =>
      rw [brute]
      split
      · -- probe branch: both children are `brute f k` at UPDATED pantries
        rename_i h
        simp only [Taste.depth]
        have h1 := ih (Function.update a ⟨k, h⟩ false)
        have h2 := ih (Function.update a ⟨k, h⟩ true)
        have := max_le h1 h2
        omega
      · -- skip branch: the strategy is unchanged
        exact le_trans (ih a) (Nat.le_succ k)
