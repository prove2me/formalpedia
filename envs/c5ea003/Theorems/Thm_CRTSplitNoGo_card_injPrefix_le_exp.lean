-- Prove2me | Theorems.Thm_CRTSplitNoGo_card_injPrefix_le_exp
-- name    : CRTSplitNoGo.card_injPrefix_le_exp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:35:37.993742+00:00
-- url     : https://prove2.me/theorems/6bd4aaf4-e029-40b0-a4f3-b90eb628ae55
-- title:
--   The birthday tail (Conjecture 1 of the previous cycle).
-- statement:
--   **The birthday tail (Conjecture 1 of the previous cycle).**  The number of maps of an
--   `n`-element set whose orbit prefix of length `T + 1` from a fixed seed is collision-free is at
--   most `exp (-T(T+1)/(2n)) · n ^ n`.  Collisions are thus *overwhelmingly* likely once
--   `T ≫ √n`: the birthday exponent `1/2` is sharp from above as well as from below.
--
--   ```lean
--   theorem CRTSplitNoGo.card_injPrefix_le_exp(a : α) (T : ℕ) (hT : T < Fintype.card α) :
--       ((injPrefixFinset a T).card : ℝ)
--         ≤ Real.exp (-((T * (T + 1) : ℝ) / (2 * Fintype.card α)))
--             * (Fintype.card α : ℝ) ^ (Fintype.card α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CRTSplitNoGoBirthdayTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CRTSplitNoGoBirthdayTail.lean#L93

-- Thm stub generated from Bridges/CRTSplitNoGoBirthdayTail.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail

/-!
# The CRT-Split No-Go, Part VII: the birthday *window* and the exact Pollard reveal time

Part VI proved the exact birthday law `card_injPrefix` for orbit prefixes and derived its
lower half (`majority_collision_free`): at time `T` with `T (T+1) ≤ n` at least half of all
`n ^ n` maps of an `n`-element set still have a collision-free orbit prefix.  That is only one
side of a threshold.  This file closes the loop by proving the matching *upper* half — an
exponential tail — and it settles the easy half of the smoothness-regime conjecture by
computing the Pollard `p-1` reveal time exactly.

## Main results

* `card_injPrefix_le_exp` — the exact birthday product is dominated by a Gaussian tail:
  `#{f : collision-free prefix of length T+1} ≤ exp (-T(T+1)/(2n)) · n ^ n`.
  This is Conjecture 1 of the previous cycle's `FUTURE_DIRECTIONS.md`, now a theorem.
* `minority_collision_free` — consequently, once `4 n ≤ T (T+1)` (i.e. `T ≳ 2√n`) at most a
  quarter of all maps are collision-free.
* `birthday_window_zmod` — the two halves together, on the state space `ZMod p` of the reduced
  dynamics: the collision-free fraction passes from `≥ 1/2` to `≤ 1/4` inside the window
  `√p ≲ T ≲ 2√p`.  The first cycle closure — the only factor-revealing event, by Parts I–IV —
  therefore happens at `T ≍ √p = N^{1/4}`, exponentially far in `log N`.
* `pm1RevealTime_eq_min_orderOf` — for `N = p q` and a base `a` invertible mod both factors
  with *distinct* multiplicative orders, the least exponent `M > 0` at which
  `gcd (a^M - 1) N` is a nontrivial factor is **exactly** `min (ord_p a) (ord_q a)`.  Part V
  gave the `≥` half; the `≤` half is the Xor criterion applied at `M = min`.  This is the
  first half of Conjecture 4, now a theorem, and it identifies the cost of regime (b) with an
  invariant of the *hidden* factors, invisible from `N`.
* `pm1RevealTime_demo` — an in-kernel instance: for `N = 341371 = 631 · 541` and `a = 2` the
  reveal time is exactly `45 = ord_631 2`.
-/

open CRTSplitNoGo

open Finset

/-! ## Part A: the exponential tail of the birthday product -/

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem CRTSplitNoGo.card_injPrefix_le_exp(a : α) (T : ℕ) (hT : T < Fintype.card α) :
    ((injPrefixFinset a T).card : ℝ)
      ≤ Real.exp (-((T * (T + 1) : ℝ) / (2 * Fintype.card α)))
          * (Fintype.card α : ℝ) ^ (Fintype.card α) := by sorry
