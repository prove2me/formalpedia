-- Prove2me | solution 1 for PadicBerggren.B1_int_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T23:05:24.326625+00:00
-- url     : https://prove2.me/submissions/b9432f0f-c173-4be4-bf47-b7aa85f2c4e8

-- Sol generated from Geometry/PadicBerggrenDynamics.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics
import Theorems.Thm_PadicBerggren_pow_unipotent_formula
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

theorem B₁_eq_one_add : B₁ R = 1 + N₁ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₁, N₁] <;> ring


theorem N₁_sq : (N₁ R) ^ 2 = !![0, 0, 0; 0, -4, 4; 0, -4, 4] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem N₁_cube : (N₁ R) ^ 3 = 0 := by
  rw [pow_succ, N₁_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three]






/-! ### Order of the unipotent generators mod `p^k` -/

/-- A natural number scalar matrix multiplies entrywise. -/
theorem natCast_matrix_mul {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (M : Matrix n n R) : ((m : Matrix n n R)) * M = (m : R) • M := by
  have h : ((m : ℕ) : Matrix n n R) = (m : R) • (1 : Matrix n n R) := by
    ext i j
    simp [Matrix.natCast_apply, Matrix.one_apply, apply_ite ((↑) : ℕ → R)]
  rw [h, Matrix.smul_mul, one_mul]


/-- For an odd prime power `p^k`, `p^k` divides the binomial coefficient `C(p^k, 2)`. -/
theorem pow_dvd_choose_two (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    p ^ k ∣ (p ^ k).choose 2 := by
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left hodd
  have hodd' : p ^ k % 2 = 1 := by simp [Nat.pow_mod, h2]
  obtain ⟨t, ht⟩ : ∃ t, p ^ k = 2 * t + 1 := ⟨p ^ k / 2, by omega⟩
  refine ⟨t, ?_⟩
  have h1 : 2 * t + 1 - 1 = 2 * t := by omega
  have key : (2 * t + 1) * (2 * t) = ((2 * t + 1) * t) * 2 := by ring
  rw [Nat.choose_two_right, ht, h1, key]
  generalize (2 * t + 1) * t = A
  omega






/-! ### The unipotent generators fix a single null line -/






/-! ## The hyperbolic generator

`B₂` is conjugate (over `ℤ[1/2]`) to `diag(−1) ⊕ U` with `U = !![3,2;4,3]`, the matrix of
multiplication by the square `3 + 2√2` of the silver ratio on `ℤ[√2]`.  We prove everything
through the concrete conjugation `B₂ · W = W · (S · emb U)`. -/


























/-! ### Frobenius on the hyperbolic block -/









/-! ### Fixed points and the split/inert dichotomy on the null cone -/




/-! ## Depth: lifting from `ZMod p` to `ZMod (p^k)` -/


open EntryDvd


theorem add {d : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A) (hB : EntryDvd d B) :
    EntryDvd d (A + B) := fun i j => by
  simpa [Matrix.add_apply] using dvd_add (hA i j) (hB i j)






/-- Scalar-matrix multiplication is entrywise multiplication (integer version). -/
theorem natCast_matrix_mul_int (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ((m : Matrix (Fin 3) (Fin 3) ℤ)) * M = (m : ℤ) • M := natCast_matrix_mul m M













/-! ## The boundary of the tree does not survive reduction

The Berggren tree is a ternary tree: `3^d` vertices at depth `d`.  Reducing mod `m` lands in a
set of size `m³`, so the reduction map on words is massively non-injective; the "boundary at
infinity" cannot be embedded in a fixed finite level `ZMod (p^k)`.  (What does survive is the
inverse-limit statement `B₂_padic_contraction`.) -/









namespace EntryDvd

theorem mono {d e : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (h : d ∣ e) (hA : EntryDvd e A) :
    EntryDvd d A := fun i j => h.trans (hA i j)

theorem add {d : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A) (hB : EntryDvd d B) :
    EntryDvd d (A + B) := fun i j => by
  simpa [Matrix.add_apply] using dvd_add (hA i j) (hB i j)

theorem mul {d e : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (hB : EntryDvd e B) : EntryDvd (d * e) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => mul_dvd_mul (hA i k) (hB k j)

theorem mul_right {d : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (B : Matrix (Fin 3) (Fin 3) ℤ) : EntryDvd d (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (hA i k) _

end EntryDvd

open PadicBerggren in
theorem solution(p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    EntryDvd ((p : ℤ) ^ k) ((B₁ ℤ) ^ (p ^ k) - 1) := by
  have hform := pow_unipotent_formula (N₁ ℤ) N₁_cube (p ^ k)
  rw [← B₁_eq_one_add] at hform
  have hsub : (B₁ ℤ) ^ (p ^ k) - 1
      = ((p ^ k : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * N₁ ℤ
        + (((p ^ k).choose 2 : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * (N₁ ℤ) ^ 2 := by
    rw [hform]
    noncomm_ring
  rw [hsub]
  refine EntryDvd.add ?_ ?_
  · rw [natCast_matrix_mul_int]
    intro i j
    refine ⟨(N₁ ℤ) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · obtain ⟨t, ht⟩ := pow_dvd_choose_two p k hp hodd
    rw [natCast_matrix_mul_int]
    intro i j
    refine ⟨(t : ℤ) * ((N₁ ℤ) ^ 2) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, ht]
    push_cast
    ring
