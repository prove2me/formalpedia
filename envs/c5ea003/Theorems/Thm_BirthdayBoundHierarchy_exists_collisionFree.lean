-- Prove2me | Theorems.Thm_BirthdayBoundHierarchy_exists_collisionFree
-- name    : BirthdayBoundHierarchy.exists_collisionFree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:02.960162+00:00
-- url     : https://prove2.me/theorems/da85818e-db48-4157-94fa-b1be986eed52
-- title:
--   Sharpness (adversary) direction.
-- statement:
--   **Sharpness (adversary) direction.**  If `k ^ r ≤ p`, the base-`k` digit
--   system makes all `k ^ r` selection sums pairwise distinct, so no collision
--   occurs.  Consequently a level-`r` search examining at most `p` selections can
--   fail.
--
--   ```lean
--   theorem BirthdayBoundHierarchy.exists_collisionFree{p k r : ℕ} (h : k ^ r ≤ p) :
--       ∃ A : Fin r → Fin k → ZMod p, Function.Injective (selSum A) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BirthdayBoundHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BirthdayBoundHierarchy.lean#L60

-- Thm stub generated from Applications/BirthdayBoundHierarchy.lean
import Mathlib
import Definitions.Def_Applications_BirthdayBoundHierarchy
import Definitions.Def_Applications_ThreeSumFactoring
/-
# The birthday-bound hierarchy of collision-based factoring

Companion to `Catalog/Applications/ThreeSumFactoring.lean`.

A *level-`r` collision search* modulo an unknown prime `p ∣ N` picks `r` families
`A 0, …, A (r-1)` of `k` residues each and looks for two distinct selections
`x ≠ y` with `∑ j, A j (x j) = ∑ j, A j (y j)` in `ZMod p`; such a collision is a
nonzero integer combination divisible by `p`, hence (Theorem
`ThreeSumFactoring.reveal_of_pos_lt`) a factor reveal.

* `r = 2` is the sumset / birthday-paradox level (`a + b ≡ c + d`),
* `r = 3` is the 3SUM level (`a + b + c ≡ a' + b' + c'`),
* `r` large is the general `r`-SUM level.

The main results are:

* `collisionGuaranteed_iff` — a level-`r` search of family size `k` is guaranteed
  to succeed **iff** `p < k ^ r`.  The forward direction is pigeonhole; the
  converse is a sharpness construction (base-`k` digits) showing that with
  `k ^ r ≤ p` an adversary can make all `k ^ r` sums distinct.
* `collisionGuaranteed_mono_level` — raising the level never costs more elements:
  the required `k` drops like `p ^ (1/r)`.  This is the "exponent improves
  `1/2 → 1/3`" row of the hierarchy table.
* `birthday_barrier_sqrt` — nevertheless the *work* `k ^ r` (the number of
  selections examined) always exceeds `p`, so for a balanced semiprime
  `N = p*q`, `q ≤ 2p`, every level satisfies `N < 2 * (k ^ r) ^ 2`: the `√N`
  barrier is level-independent.
* `evaluation_barrier` — the same bound for the third row of the table, an
  exhaustive evaluation search that must hit a prescribed residue class.
-/

open BirthdayBoundHierarchy

open Finset

/-! ## Level-`r` collisions -/

theorem BirthdayBoundHierarchy.exists_collisionFree{p k r : ℕ} (h : k ^ r ≤ p) :
    ∃ A : Fin r → Fin k → ZMod p, Function.Injective (selSum A) := by sorry
