-- Prove2me | solution 1 for PadicBerggren.B2_pow_eq_one_of_block
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T22:59:59.259122+00:00
-- url     : https://prove2.me/submissions/4dec77f9-c76b-4b85-958e-a1a43d4fc29e

-- Sol generated from Geometry/PadicBerggrenDynamics.lean
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
* `B₁_fixes_null_line`, `B₁_fixed_iff` : `B₁` fixes exactly the null line spanned by `(0,1,1)`
  (a boundary point of the light cone), and `B₃` fixes the null line `(1,0,1)`.

Hyperbolic generator (p odd):

* `Um_pow_card` : Frobenius applied to the hyperbolic `2×2` block `U = !![3,2;4,3] = 3 + 2J`,
  `J² = 2` : `U^p = 3 + 2·(2^((p−1)/2))·J`.
* `B₂_pow_p_sub_one_of_isSquare_two` / `B₂_pow_p_add_one_of_not_isSquare_two` :
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













theorem emb_one : emb (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb]

theorem emb_mul (A B : Matrix (Fin 2) (Fin 2) R) : emb (A * B) = emb A * emb B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem emb_pow (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : emb (A ^ n) = (emb A) ^ n := by
  induction n with
  | zero => simpa using emb_one (R := R)
  | succ n ih => rw [pow_succ, emb_mul, ih, pow_succ]




theorem Sm_sq : (Sm R) ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Matrix.mul_apply, Fin.sum_univ_three]

theorem Sm_pow_even {m : ℕ} (hm : Even m) : (Sm R) ^ m = 1 := by
  obtain ⟨t, ht⟩ := hm
  rw [show m = 2 * t by omega, pow_mul, Sm_sq, one_pow]

theorem Sm_commute_emb_Um : Commute (Sm R) (emb (Um R)) := by
  unfold Commute SemiconjBy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three]

theorem B₂_mul_Wm : B₂ R * Wm R = Wm R * (Sm R * emb (Um R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, Wm, Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem Wm_mul_Vm : (Wm R) * Vm R = (2 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wm, Vm, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem B₂_pow_mul_Wm (n : ℕ) : (B₂ R) ^ n * Wm R = Wm R * (Sm R * emb (Um R)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, B₂_mul_Wm, ← mul_assoc, ih, mul_assoc, ← pow_succ]


/-! ### Frobenius on the hyperbolic block -/









/-! ### Fixed points and the split/inert dichotomy on the null cone -/




/-! ## Depth: lifting from `ZMod p` to `ZMod (p^k)` -/


open EntryDvd





















/-! ## The boundary of the tree does not survive reduction

The Berggren tree is a ternary tree: `3^d` vertices at depth `d`.  Reducing mod `m` lands in a
set of size `m³`, so the reduction map on words is massively non-injective; the "boundary at
infinity" cannot be embedded in a fixed finite level `ZMod (p^k)`.  (What does survive is the
inverse-limit statement `B₂_padic_contraction`.) -/









open PadicBerggren in
theorem solution(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {m : ℕ}
    (hU : (Um (ZMod p)) ^ m = 1) (hm : Even m) : (B₂ (ZMod p)) ^ m = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hblock : (Sm (ZMod p) * emb (Um (ZMod p))) ^ m = 1 := by
    rw [Commute.mul_pow Sm_commute_emb_Um, Sm_pow_even hm, ← emb_pow, hU, emb_one, one_mul]
  have key : (B₂ (ZMod p)) ^ m * Wm (ZMod p) = Wm (ZMod p) := by
    rw [B₂_pow_mul_Wm, hblock, mul_one]
  have key2 : (B₂ (ZMod p)) ^ m * ((2 : ZMod p) • 1) = (2 : ZMod p) • 1 := by
    rw [← Wm_mul_Vm, ← mul_assoc, key]
  rw [Matrix.mul_smul, mul_one] at key2
  ext i j
  have := congrFun (congrFun key2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ h2 this
