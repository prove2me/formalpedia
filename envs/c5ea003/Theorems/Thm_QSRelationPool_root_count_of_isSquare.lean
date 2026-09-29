-- Prove2me | Theorems.Thm_QSRelationPool_root_count_of_isSquare
-- name    : QSRelationPool.root_count_of_isSquare
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:24.839318+00:00
-- url     : https://prove2.me/theorems/cb7b72dd-03af-4fa7-b949-a342145edbee
-- title:
--   Admissible primes hit twice per period.
-- statement:
--   **Admissible primes hit twice per period.**  If `N` is a nonzero square mod
--   an odd prime `p`, then exactly `2` of the `p` residues `x` give `p â£ x^2 - N`.
--
--   ```lean
--   theorem QSRelationPool.root_count_of_isSquare(hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0)
--       (hsq : IsSquare a) : rootCount p a = 2 := by sorry
--
--
--   /-! ## The exact cancellation -/
--
--
--
--
--
--   /-! ## Lab notes: machine-checked instances of the identities
--
--   The following finite checks are verified by the kernel (`decide`), and are the
--   small-scale instances of the theorems above; they reproduce, exactly, the
--   `hitcounts ∈ {0,1,2}`, `#admissible = (p-1)/2`, `total = p` pattern measured
--   numerically in `ComputationalEvidence.md` for `p = 7, 11, 13, 17, 19, 31`. -/
--
--
--   /-- `p = 7`, `N ≡ 2`: an admissible modulus is hit twice per period. -/
--   example : (Finset.univ.filter (fun x : ZMod 7 => x ^ 2 = 2)).card = 2 := by decide
--
--   /-- `p = 7`, `N ≡ 3`: an inadmissible modulus is never hit. -/
--   example : (Finset.univ.filter (fun x : ZMod 7 => x ^ 2 = 3)).card = 0 := by decide
--
--   /-- `p = 11`: exactly `(11-1)/2 = 5` nonzero admissible residues. -/
--   example :
--       (Finset.univ.filter (fun a : ZMod 11 => a ≠ 0 ∧ ∃ x : ZMod 11, x ^ 2 = a)).card = 5 := by
--     decide
--
--   /-- `p = 13`: the total hit count over a full period of moduli is `13`
--   (`expected_hits_eq_one`). -/
--   example : ∑ a : ZMod 13, (Finset.univ.filter (fun x : ZMod 13 => x ^ 2 = a)).card = 13 := by
--     decide
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/QSRelationPoolRandom.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/QSRelationPoolRandom.lean#L92

-- Thm stub generated from Shared/QSRelationPoolRandom.lean
import Mathlib
import Definitions.Def_Shared_QSRelationPoolRandom

/-!
# The quadratic-sieve relation pool is *exactly* random-equivalent, prime by prime

Context (experiment 465, paper 130).  In the quadratic sieve one factors the
values `v(x) = x^2 - N` over a factor base of primes `p ≤ B`, and one models the
probability that `v(x)` is `B`-smooth by the probability that a *random* integer
of the same size is `B`-smooth.  This looks suspicious, because the values
`x^2 - N` are **not** random: an odd prime `p ∤ N` can divide `x^2 - N` only when
`N` is a quadratic residue mod `p`, i.e. only *half* the primes are admissible at
all.  The empirical finding of the experiment is that, nevertheless, the pool
behaves exactly like a random pool of the same size at every scale tested
(`N ∈ {2^32 .. 2^44}`, ratio `0.993–1.020`).

This file proves the exact algebraic identity that *explains* that measurement:

* only half of the nonzero residues `N` are admissible
  (`card_admissible_residues`), but
* each admissible prime hits **twice** as often per period
  (`root_count_of_isSquare`), and
* the two effects cancel **exactly**, not just to leading order
  (`relation_pool_random_equivalent`, `expected_hits_eq_one`):
  the average, over the residue of `N`, of the number of `x` per period `p` with
  `p ∣ x^2 - N` is exactly `1` — the same as for a random integer sequence.

Main results:

* `dvd_qsValue_iff_sq_eq` — the arithmetic of the pool transported to `ZMod p`.
* `isSquare_of_dvd_qsValue` — the quadratic-character constraint on divisors.
* `exists_dvd_qsValue_iff_isSquare` — the constraint is *exactly* the obstruction.
* `root_count_of_isSquare` / `root_count_of_not_isSquare` — the `2`/`0` dichotomy.
* `card_admissible_residues` — exactly `(p-1)/2` admissible nonzero residues.
* `relation_pool_random_equivalent` — the exact cancellation `2 · (p-1)/2 = p-1`.
* `expected_hits_eq_one` — total hit count over a full period of residues is `p`.
-/

open QSRelationPool

open Finset



/-! ## Transporting the pool to `ZMod p` -/




/-! ## The `2`/`0` dichotomy for the local hit count -/

variable {p : ℕ} [Fact p.Prime]

theorem QSRelationPool.root_count_of_isSquare(hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0)
    (hsq : IsSquare a) : rootCount p a = 2 := by sorry
