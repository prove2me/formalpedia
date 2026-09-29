-- Prove2me | Definitions.Def_Applications_BirthdayBoundHierarchy
-- name    : Applications_BirthdayBoundHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:36:54.935315+00:00
-- url     : https://prove2.me/theorems/03b31e75-9e6b-47be-bb54-cecfcd393d9e
-- title:
--   Aether Catalog definitions — Applications_BirthdayBoundHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BirthdayBoundHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BirthdayBoundHierarchy.lean by skeleton subtraction
import Mathlib
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

namespace BirthdayBoundHierarchy

open Finset

/-! ## Level-`r` collisions -/

/-- The sum of the selection `x` against the family system `A`. -/
def selSum {p k r : ℕ} (A : Fin r → Fin k → ZMod p) (x : Fin r → Fin k) : ZMod p :=
  ∑ j, A j (x j)

/-- A level-`r` search with family size `k` is *guaranteed* modulo `p` if **every**
system of `r` families of `k` residues admits two distinct selections with equal
sum. -/
def CollisionGuaranteed (p k r : ℕ) : Prop :=
  ∀ A : Fin r → Fin k → ZMod p, ∃ x y : Fin r → Fin k, x ≠ y ∧ selSum A x = selSum A y




/-! ## The hierarchy: the exponent improves, the work does not -/





/-! ## Translation to the `√N` barrier -/



/-! ## Third row: exhaustive evaluation searches -/



/-! ## From a collision to an actual factor -/



end BirthdayBoundHierarchy


