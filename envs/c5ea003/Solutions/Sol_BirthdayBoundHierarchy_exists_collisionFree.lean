-- Prove2me | solution 1 for BirthdayBoundHierarchy.exists_collisionFree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:48:53.314781+00:00
-- url     : https://prove2.me/submissions/15d6836f-721a-40a8-837e-6ec9d8066482

-- Sol generated from Applications/BirthdayBoundHierarchy.lean
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






/-! ## The hierarchy: the exponent improves, the work does not -/





/-! ## Translation to the `√N` barrier -/



/-! ## Third row: exhaustive evaluation searches -/



/-! ## From a collision to an actual factor -/




open BirthdayBoundHierarchy in
theorem solution{p k r : ℕ} (h : k ^ r ≤ p) :
    ∃ A : Fin r → Fin k → ZMod p, Function.Injective (selSum A) := by
  refine ⟨fun j i => ((i : ℕ) * k ^ (j : ℕ) : ℕ), ?_⟩
  intro x y hxy
  have key : ∀ z : Fin r → Fin k,
      selSum (fun j i => (((i : ℕ) * k ^ (j : ℕ) : ℕ) : ZMod p)) z
        = ((finFunctionFinEquiv z : ℕ) : ZMod p) := by
    intro z
    rw [finFunctionFinEquiv_apply]
    simp [selSum, Nat.cast_sum]
  rw [key x, key y] at hxy
  have hx : (finFunctionFinEquiv x : ℕ) < p :=
    lt_of_lt_of_le (finFunctionFinEquiv x).isLt h
  have hy : (finFunctionFinEquiv y : ℕ) < p :=
    lt_of_lt_of_le (finFunctionFinEquiv y).isLt h
  have : (finFunctionFinEquiv x : ℕ) = (finFunctionFinEquiv y : ℕ) := by
    have := congrArg ZMod.val hxy
    rwa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] at this
  have : (finFunctionFinEquiv x : Fin (k ^ r)) = finFunctionFinEquiv y := Fin.ext this
  exact finFunctionFinEquiv.injective this
