-- Prove2me | solution 1 for Hashimoto.Examples.C5_closedNBWalks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:36:41.33136+00:00
-- url     : https://prove2.me/submissions/ae3ffb01-f531-4e0e-8651-3618d6668906

-- Sol generated from Algebra/NonBacktracking/Examples.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_Examples
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Theorems.Thm_Hashimoto_trace_hashimoto
import Theorems.Thm_Hashimoto_trace_hashimoto_pow
import Theorems.Thm_Hashimoto_trace_hashimoto_sq

/-!
# Worked examples of the non-backtracking trace formula

Concrete graphs on which the counting theorem
`trace (B ^ n) = #{rooted closed non-backtracking walks of length n}` is exercised.

* the **triangle** `K₃`: its Hashimoto matrix is a permutation matrix of order `3`
  (`Hashimoto.Examples.K3_hashimoto_pow_three`), whence the exact periodic count
  `trace (B ^ n) = 6` if `3 ∣ n` and `0` otherwise;
* the **complete graph** `K₄`: `trace (B³) = 24 = 6 · 4` (four triangles) and
  `trace (B⁴) = 24 = 8 · 3` (three quadrilaterals);
* the **path** `P₃`, a tree: `B² = 0`, so a tree has no closed non-backtracking walk
  of any length.

All numeric statements are checked by kernel evaluation (`decide`) and then combined
with the general theorems, so no example is a bare computation.
-/

open Hashimoto.Examples

open Hashimoto

/-! ## The triangle -/


instance : DecidableRel K3.Adj := fun a b => by unfold K3; infer_instance







/-! ## The complete graph on four vertices -/


instance : DecidableRel K4.Adj := fun a b => by unfold K4; infer_instance



/-! ## The pentagon -/


instance : DecidableRel C5.Adj := fun a b => by unfold C5 SimpleGraph.fromRel; infer_instance

set_option maxHeartbeats 2000000 in
/-- On a cycle graph every dart has a unique continuation; for `C₅` the resulting
permutation of the ten darts has order five (two `5`-cycles: one per orientation). -/
theorem C5_hashimoto_pow_five : hashimoto C5 ^ 5 = 1 := by decide

theorem C5_card_darts : Fintype.card C5.Dart = 10 := by decide

set_option maxHeartbeats 1000000 in
/-- `C₅` has no closed non-backtracking walk of length three. -/
theorem C5_trace_pow_three : (hashimoto C5 ^ 3).trace = 0 := by decide

set_option maxHeartbeats 2000000 in
/-- `C₅` has no closed non-backtracking walk of length four. -/
theorem C5_trace_pow_four : (hashimoto C5 ^ 4).trace = 0 := by decide


/-! ## A tree -/


instance : DecidableRel P3.Adj := fun a b => by unfold P3 SimpleGraph.fromRel; infer_instance




open Hashimoto.Examples in
theorem solution(n : ℕ) (hn : 1 ≤ n) :
    (closedNBWalks C5 n).card = if 5 ∣ n then 10 else 0 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 5 ∧ n = 5 * k + r :=
    ⟨n / 5, n % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [← trace_hashimoto_pow, pow_add, pow_mul, C5_hashimoto_pow_five, one_pow, one_mul]
  interval_cases r
  · rw [pow_zero, Matrix.trace_one, C5_card_darts, if_pos (by omega)]
    norm_num
  · rw [if_neg (by omega)]
    exact trace_hashimoto C5
  · rw [if_neg (by omega)]
    exact trace_hashimoto_sq C5
  · rw [if_neg (by omega)]
    exact C5_trace_pow_three
  · rw [if_neg (by omega)]
    exact C5_trace_pow_four
