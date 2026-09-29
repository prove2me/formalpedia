-- Prove2me | solution 1 for JacSign.WZ_eq_WN
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:05:51.64975+00:00
-- url     : https://prove2.me/submissions/a5984af4-9a77-41f5-8692-725a2dd9f4e9

-- Sol generated from Tropical/JacobiSignedNonDial.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedMultiplicative
import Definitions.Def_Tropical_JacobiSignedNonDial

/-!
# The Jacobi-signed circle count escapes the residue dial

The earlier character-weighted witnesses (CIRC, BQF, GSP) all collapsed to a *residue
dial*: their value was a function of `N mod 4` or `N mod 8`.  Here we prove, by exact
evaluation, that the Jacobi-signed count is **not** a residue dial, and that the Weil
floor of `JacobiSignedWeilFloorBound.lean` is nearly attained.

* `JacSign.WZ_eq_WN` : the abstract statistic equals the concrete range-sum, so all the
  numerical statements below are statements about `W` / `WZ` themselves.
* `JacSign.W_17`, `JacSign.W_41`, ... : exact values (`-2`, `-10`, `-14`, ...).
* `JacSign.not_residue_dial_prime` : there is **no** function `f` with `W p = f (p % 8)`
  for all primes `p`.  (`17 ≡ 41 ≡ 1 (mod 8)` but `W 17 = -2 ≠ -10 = W 41`.)
* `JacSign.not_residue_dial_modulus` : likewise at composite level
  (`21 ≡ 85 ≡ 5 (mod 8)` but `WZ 21 = 0 ≠ -4 = WZ 85`).
* `JacSign.weil_floor_near_attained` : `W 173 = 26` and `26² = 676 > 0.97 · (4 · 173)`,
  so the bound `W p ^ 2 ≤ 4 p` cannot be improved by any constant factor `< 0.977`.
* `JacSign.not_constant_on_primes_mod_four` : the statistic is not a dial mod 4 either.
-/

open Finset

open JacSign





set_option maxRecDepth 100000




















open JacSign in
theorem solution(n : ℕ) [NeZero n] : WZ n = WN n := by
  rw [WZ, WN]
  refine Finset.sum_nbij' (i := fun x : ZMod n => x.val) (j := fun k : ℕ => (k : ZMod n))
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro k _; exact Finset.mem_univ _
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
  · intro a _
    show jchar n _ = jacobiSym ((a.val : ℤ) * (1 - (a.val : ℤ) ^ 2)) n
    unfold jchar
    apply jacobiSym.mod_left'
    refine (ZMod.intCast_eq_intCast_iff' (((a * (1 - a ^ 2)).val : ℤ))
      ((a.val : ℤ) * (1 - (a.val : ℤ) ^ 2)) n).mp ?_
    push_cast
    simp
