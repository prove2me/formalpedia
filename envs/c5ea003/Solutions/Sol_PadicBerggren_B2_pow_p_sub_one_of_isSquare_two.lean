-- Prove2me | solution 1 for PadicBerggren.B2_pow_p_sub_one_of_isSquare_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T23:22:40.788044+00:00
-- url     : https://prove2.me/submissions/03ca5683-0d81-4f36-a952-7438da24fec3

-- Thm stub generated from Geometry/PadicBerggrenDynamics.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Theorems.Thm_PadicBerggren_B2_pow_eq_one_of_block

/-!
# p-adic Berggren dynamics

The Berggren (Barning–Hall) moves are the three integer matrices

```
B₁ = !![1,-2,2; 2,-1,2; 2,-2,3]   B₂ = !![1,2,2; 2,1,2; 2,2,3]   B₃ = !![-1,2,2; -2,1,2; -2,2,3]
```

acting on column vectors `(a,b,c)` and generating the ternary tree of primitive Pythagorean
triples.  They preserve the Lorentz form `q(a,b,c) = a² + b² − c²`.  The catalog already
contains the real/hyperbolic geometry of the tree and the exact spectral data of the
generators over `ℤ` (`Catalog/Cryptography/BerggrenSpectral/Generators.lean`:
`charpoly B₁ = charpoly B₃ = (X−1)³`, `charpoly B₂ = (X+1)(X²−6X+1)`).

This file develops the **p-adic / mod `p^k` dynamics** of the same three matrices.  Everything
below is proved for the reductions of the *same* generators, over `ZMod (p^k)`.

## Main results

Structural (any commutative ring `R`):

* `lorentz_B₁`, `lorentz_B₂`, `lorentz_B₃` : the moves preserve `a² + b² − c²` over any `R`;
  in particular the null cone mod `p^k` is invariant.
* `bijOn_nullCone_B₁/₂/₃` : each move is a *bijection* of the null cone; mod `p^k` the tree
  therefore becomes a finite invertible dynamical system.
* `B₁_eq_one_add`, `N₁_cube`, `N₁_sq_ne_zero` : `B₁ = 1 + N₁` with `N₁³ = 0`, and the
  nilpotency index is exactly `3` **iff `4 ≠ 0`** in `R`.  Mod `2` and mod `4` the index drops
  to `2`: the unipotent p-adic classification is uniform except at the prime `2`.

Unipotent generators (p odd):

* `pow_unipotent_formula` : `(1+X)^n = 1 + n X + C(n,2) X²` whenever `X³ = 0`.
* `B₁_pow_p_pow`, `B₃_pow_p_pow` : `B₁^(p^k) = 1` and `B₃^(p^k) = 1` in `ZMod (p^k)`.
* `B₁_order_exact` : conversely `B₁^m = 1` mod `p^k` forces `p^k ∣ m`, so the order of `B₁`
  mod `p^k` is *exactly* `p^k` — a pure `p`-power ("pro-`p`", nilpotent behaviour).
* `B₁_pow_ne_one_padic` : sharpness of the depth — `B₁^(p^k) = 1` mod `p^k` but not mod
  `p^(k+1)`.
* `B₁_fixes_null_line`, `B1_fixed_iff` : `B₁` fixes exactly the null line spanned by `(0,1,1)`
  (a boundary point of the light cone), and `B₃` fixes the null line `(1,0,1)`.

Hyperbolic generator (p odd):

* `Um_pow_card` : Frobenius applied to the hyperbolic `2×2` block `U = !![3,2;4,3] = 3 + 2J`,
  `J² = 2` : `U^p = 3 + 2·(2^((p−1)/2))·J`.
* `B₂_pow_p_sub_one_of_isSquare_two` / `B2_pow_p_add_one_of_not_isSquare_two` :
  the order of `B₂` mod `p` divides `p − 1` if `2` is a square mod `p` and divides `p + 1`
  otherwise.  By quadratic reciprocity this is decided by `p mod 8`.
* `B₂_pow_card_sq_sub_one`, `B₂_orderOf_dvd` : in all cases the order divides `p² − 1`,
  confirming the conjectured bound.
* `B₂_null_eigenvector_iff_isSquare_two`, `B₂_null_eigenvector_iff_mod_eight` :
  `B₂` has a nonzero eigenvector **on the null cone** iff `2` is a square mod `p`, iff
  `p ≡ ±1 (mod 8)`.  This is the exact p-adic split/inert (hyperbolic/elliptic) dichotomy.
* `B₂_no_nonzero_fixed_point` : `B₂` has no nonzero fixed vector mod `p`, in sharp contrast
  with the unipotent generators.

Depth (`p^k`) statements:

* `lift_pow` : an entrywise Hensel lift, `A ≡ 1 (mod p) → A^(p^k) ≡ 1 (mod p^(k+1))`.
* `B₂_pow_eq_one_padic` : `B₂^((p²−1)·p^(k−1)) = 1` in `ZMod (p^k)`.
* `B₂_padic_contraction` : the p-adic distance `|B₂^N v − v|_p ≤ p^(−k)` for `N = (p²−1)p^(k−1)`
  and every integer vector `v`: the hyperbolic generator is *periodic to any p-adic precision*.
* `tree_collision_mod` : the `3^d` words of length `d` collide mod `m` as soon as `m³ < 3^d`,
  so the reduction of the boundary of the tree is **not** injective: there is no p-adic Cantor
  set inside a fixed finite level `ZMod (p^k)` (see `FUTURE_DIRECTIONS.md`).
-/

open PadicBerggren

open Matrix

/-! ## The generators and the Lorentz form -/

variable (R : Type*) [CommRing R]












variable {R : Type*} [CommRing R]







/-! ### Determinants and inverses -/










/-! ### The moves are bijections of the null cone

Over `ZMod (p^k)` the null cone is a finite set, so each Berggren move becomes a permutation
of a finite set: the tree reduces to an invertible finite dynamical system. -/





/-! ## Unipotent generators -/










/-! ### Order of the unipotent generators mod `p^k` -/









/-! ### The unipotent generators fix a single null line -/






/-! ## The hyperbolic generator

`B₂` is conjugate (over `ℤ[1/2]`) to `diag(−1) ⊕ U` with `U = !![3,2;4,3]`, the matrix of
multiplication by the square `3 + 2√2` of the silver ratio on `ℤ[√2]`.  We prove everything
through the concrete conjugation `B₂ · W = W · (S · emb U)`. -/


























/-! ### Frobenius on the hyperbolic block -/
theorem scal2_commute (a : R) (M : Matrix (Fin 2) (Fin 2) R) : Commute (scal2 a) M := by
  unfold Commute SemiconjBy scal2
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

theorem scal2_eq (c : R) : scal2 c = !![c, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal2]

theorem scal2_mul (a b : R) : scal2 a * scal2 b = scal2 (a * b) := by
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scal2_pow (a : R) (n : ℕ) : (scal2 a) ^ n = scal2 (a ^ n) := by
  induction n with
  | zero => simp [scal2]
  | succ n ih => rw [pow_succ, ih, scal2_mul, pow_succ]

theorem Jm_sq : (Jm R) ^ 2 = scal2 (2 : R) := by
  rw [pow_two]
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Jm_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Jm (ZMod p)) ^ p = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have hp' : p = 2 * (p / 2) + 1 := by omega
  calc (Jm (ZMod p)) ^ p = ((Jm (ZMod p)) ^ 2) ^ (p / 2) * Jm (ZMod p) := by
        rw [← pow_mul, ← pow_succ]; exact congrArg _ hp'
    _ = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by rw [Jm_sq, scal2_pow]

theorem Um_decomp : Um R = scal2 (3 : R) + scal2 (2 : R) * Jm R := by
  simp only [scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Um, Jm]; try ring)

theorem Um_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Um (ZMod p)) ^ p
      = scal2 (3 : ZMod p) + scal2 (2 * (2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hcomm : Commute (scal2 (3 : ZMod p)) (scal2 (2 : ZMod p) * Jm (ZMod p)) :=
    scal2_commute _ _
  rw [Um_decomp, add_pow_char_of_commute p hcomm,
    Commute.mul_pow (scal2_commute (2 : ZMod p) (Jm (ZMod p))), scal2_pow, scal2_pow,
    Jm_pow_card p hp, ZMod.pow_card, ZMod.pow_card, ← mul_assoc, scal2_mul]

theorem Um_mul_inv : Um R * !![3, -2; -4, 3] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem two_pow_div_two_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ^ (p / 2) = 1 ∨ (2 : ZMod p) ^ (p / 2) = -1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have hsq : ((2 : ZMod p) ^ (p / 2)) * ((2 : ZMod p) ^ (p / 2)) = 1 := by
    rw [← pow_add]
    have : p / 2 + p / 2 = p - 1 := by omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one h2
  exact mul_self_eq_one_iff.mp hsq


open PadicBerggren in
theorem solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : IsSquare (2 : ZMod p)) : (B₂ (ZMod p)) ^ (p - 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have heps : (2 : ZMod p) ^ (p / 2) = 1 := (ZMod.euler_criterion p h2).mp h
  have hUp : (Um (ZMod p)) ^ p = Um (ZMod p) := by
    rw [Um_pow_card p hp, heps, mul_one, ← Um_decomp]
  have hU : (Um (ZMod p)) ^ (p - 1) = 1 := by
    have hsplit : (Um (ZMod p)) ^ p = (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) := by
      rw [← pow_succ]
      congr 1
      omega
    have : (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) = Um (ZMod p) := by rw [← hsplit, hUp]
    calc (Um (ZMod p)) ^ (p - 1)
        = (Um (ZMod p)) ^ (p - 1) * (Um (ZMod p) * !![3, -2; -4, 3]) := by
          rw [Um_mul_inv, mul_one]
      _ = ((Um (ZMod p)) ^ (p - 1) * Um (ZMod p)) * !![3, -2; -4, 3] := by rw [mul_assoc]
      _ = Um (ZMod p) * !![3, -2; -4, 3] := by rw [this]
      _ = 1 := Um_mul_inv
  refine B2_pow_eq_one_of_block p hp hU ?_
  exact (Nat.even_sub (by omega)).mpr (by simp [Nat.not_even_iff.mpr hmod])
