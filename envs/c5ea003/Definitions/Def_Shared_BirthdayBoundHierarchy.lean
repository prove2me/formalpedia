-- Prove2me | Definitions.Def_Shared_BirthdayBoundHierarchy
-- name    : Shared_BirthdayBoundHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:30.852226+00:00
-- url     : https://prove2.me/theorems/7e66d6f7-7cc9-4b68-8a3c-6d6adbbff1c4
-- title:
--   Aether Catalog definitions — Shared_BirthdayBoundHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.BirthdayBoundHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/BirthdayBoundHierarchy.lean by skeleton subtraction
import Mathlib

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

namespace BirthdayHierarchy

open Finset

variable {α : Type*}

/-! ## Pigeonhole: large search spaces always collide -/



/-! ## Adversary: small search spaces need not collide -/


/-! ## The collapse: the threshold is the *size of the search space* -/



/-! ## The `r`-SUM instance of the hierarchy -/

/-- The search space of the `r`-SUM scheme built from a set `A`: all functions
`Fin r → A`, i.e. all `r`-tuples of elements of `A`. -/
noncomputable def tupleSpace (r : ℕ) (A : Finset ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun _ : Fin r => A)




/-! ## The `√N` barrier -/




/-! ## The exponent really does improve (stored elements) -/





end BirthdayHierarchy


