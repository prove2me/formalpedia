-- Prove2me | solution 1 for BirthdayHierarchy.card_tupleSpace
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:20:41.79637+00:00
-- url     : https://prove2.me/submissions/88778891-259c-46bd-8d0f-cec3834c9fba

-- Sol generated from Shared/BirthdayBoundHierarchy.lean
import Mathlib
import Definitions.Def_Shared_BirthdayBoundHierarchy

/-!
# The birthday-bound hierarchy and its collapse

Collision-based factoring methods (sumset collisions `a + b ≡ c + d`, 3SUM
collisions `a + b + c ≡ d + e + f`, and more generally `r`-SUM collisions) all
consist of evaluating a residue map on a search space and waiting for a
repeated value.  Increasing the arity `r` makes the search space grow like
`k^r`, so the *number of stored elements* `k` needed for a guaranteed collision
drops from `p^{1/2}` (`r = 2`) to `p^{1/3}` (`r = 3`) and beyond.

The main theorem of this file, `collision_threshold_iff`, says that this is an
illusion as far as *work* is concerned: for a search space `S` and modulus `p`,
a collision is guaranteed **iff** `p < S.card`, a criterion that mentions only
the cardinality of the search space — i.e. the number of tuples inspected —
and never the arity `r`.  The threshold is exactly `p + 1` for every scheme.

Combined with `p ≥ √N` for the larger factor of `N = p * q`, every member of
the hierarchy must inspect more than `√N` tuples: the exponent improves, the
barrier does not move.

Main results:

* `exists_collision_of_card_lt` — pigeonhole (upper bound side).
* `exists_injOn_of_card_le` — adversarial residue map (lower bound side).
* `collision_threshold_iff` — the threshold is `p + 1`, independent of arity.
* `exists_tuple_sum_collision` — the `r`-SUM instance: `p < k ^ r` suffices.
* `tuple_scheme_cost_gt_sqrt` — every scheme must inspect more than `√N` tuples.
* `cube_threshold_997`, `square_threshold_997`, `exponent_gap_997` — the
  quantitative `p^{1/2} → p^{1/3}` improvement in stored elements at `p = 997`.
-/

open BirthdayHierarchy

open Finset

variable {α : Type*}

/-! ## Pigeonhole: large search spaces always collide -/



/-! ## Adversary: small search spaces need not collide -/


/-! ## The collapse: the threshold is the *size of the search space* -/



/-! ## The `r`-SUM instance of the hierarchy -/





/-! ## The `√N` barrier -/




/-! ## The exponent really does improve (stored elements) -/






open BirthdayHierarchy in
@[simp] theorem solution(r : ℕ) (A : Finset ℕ) :
    (tupleSpace r A).card = A.card ^ r := by
  simp [tupleSpace]
