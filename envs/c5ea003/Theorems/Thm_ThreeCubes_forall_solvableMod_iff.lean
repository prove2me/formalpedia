-- Prove2me | Theorems.Thm_ThreeCubes_forall_solvableMod_iff
-- name    : ThreeCubes.forall_solvableMod_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:13:15.031506+00:00
-- url     : https://prove2.me/theorems/acced5b1-a307-46a4-ae45-08ce012bb1ab
-- title:
--   `9` is the only obstructing modulus.
-- statement:
--   **`9` is the only obstructing modulus.**  Every integer is a sum of three cubes modulo
--   `m` precisely when `9` does not divide `m`.
--
--   ```lean
--   theorem ThreeCubes.forall_solvableMod_iff{m : ℕ} (hm : 0 < m) :
--       (∀ n : ℤ, SolvableMod m n) ↔ ¬ (9 ∣ m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Moduli.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Moduli.lean#L31

-- Thm stub generated from Probability/Moduli.lean
import Mathlib
import Definitions.Def_Probability_Basic

/-!
# `9` is the unique obstructing modulus, and five cubes always suffice

Two complements to the local theory.

* `ThreeCubes.forall_solvableMod_iff` : for a positive modulus `m`, *every* integer is a sum
  of three cubes modulo `m` **iff** `9 ∤ m`.  So among all moduli, `9` (and its multiples)
  is the unique source of congruence obstructions for `x³ + y³ + z³`.

* `ThreeCubes.isSumOfFiveCubes` : **every** integer is a sum of five integer cubes.  Together
  with the mod `9` obstruction this pins the "waring number for cubes over `ℤ`" between `4`
  and `5`; the identity `6k = (k+1)³ + (k-1)³ + (-k)³ + (-k)³` also shows every multiple of
  `6` is a sum of four cubes.
-/

open ThreeCubes

/-! ### Solvability modulo `3` -/

theorem ThreeCubes.forall_solvableMod_iff{m : ℕ} (hm : 0 < m) :
    (∀ n : ℤ, SolvableMod m n) ↔ ¬ (9 ∣ m) := by sorry
