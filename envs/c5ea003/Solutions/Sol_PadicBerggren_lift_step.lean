-- Prove2me | solution 1 for PadicBerggren.lift_step
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T06:03:47.869018+00:00
-- url     : https://prove2.me/submissions/30a7d013-dc75-4b5d-85db-800c54a6fe18

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


























/-! ### Frobenius on the hyperbolic block -/









/-! ### Fixed points and the split/inert dichotomy on the null cone -/




/-! ## Depth: lifting from `ZMod p` to `ZMod (p^k)` -/


open EntryDvd

open Matrix
open Matrix Finset
namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₁ (v : Fin 3 → R) : lorentz R (B₁ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₂ (v : Fin 3 → R) : lorentz R (B₂ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₃ (v : Fin 3 → R) : lorentz R (B₃ R *ᵥ v) = lorentz R v := by
  simp [lorentz, B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₁ (v : Fin 3 → R) : lorentz R (C₁ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₂ (v : Fin 3 → R) : lorentz R (C₂ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_C₃ (v : Fin 3 → R) : lorentz R (C₃ R *ᵥ v) = lorentz R v := by
  simp [lorentz, C₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₁ : (B₁ R).det = 1 := by simp [B₁, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₂ : (B₂ R).det = -1 := by simp [B₂, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem det_B₃ : (B₃ R).det = 1 := by simp [B₃, Matrix.det_fin_three]; ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_mul_C₁ : B₁ R * C₁ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, C₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₁_mul_B₁ : C₁ R * B₁ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₁, C₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_mul_C₂ : B₂ R * C₂ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, C₂, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₂_mul_B₂ : C₂ R * B₂ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, C₂, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_mul_C₃ : B₃ R * C₃ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₃, C₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem C₃_mul_B₃ : C₃ R * B₃ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₃, C₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_of_inverse (M N : Matrix (Fin 3) (Fin 3) R) (hMN : M * N = 1) (hNM : N * M = 1)
    (hM : ∀ v, lorentz R (M *ᵥ v) = lorentz R v)
    (hN : ∀ v, lorentz R (N *ᵥ v) = lorentz R v) :
    Set.BijOn (fun v => M *ᵥ v) (nullCone R) (nullCone R) := by
  refine ⟨fun v hv => ?_, fun v _ w _ h => ?_, fun w hw => ⟨N *ᵥ w, ?_, ?_⟩⟩
  · simpa [nullCone, Set.mem_setOf_eq, hM v] using hv
  · have := congrArg (fun u => N *ᵥ u) h
    simpa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using this
  · simpa [nullCone, Set.mem_setOf_eq, hN w] using hw
  · simp [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₁ : Set.BijOn (fun v => B₁ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₁_mul_C₁ PadicBerggren.C₁_mul_B₁ PadicBerggren.lorentz_B₁ PadicBerggren.lorentz_C₁

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₂ : Set.BijOn (fun v => B₂ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₂_mul_C₂ PadicBerggren.C₂_mul_B₂ PadicBerggren.lorentz_B₂ PadicBerggren.lorentz_C₂

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem bijOn_nullCone_B₃ : Set.BijOn (fun v => B₃ R *ᵥ v) (nullCone R) (nullCone R) :=
  bijOn_of_inverse _ _ PadicBerggren.B₃_mul_C₃ PadicBerggren.C₃_mul_B₃ PadicBerggren.lorentz_B₃ PadicBerggren.lorentz_C₃

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_eq_one_add : B₁ R = 1 + N₁ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₁, N₁] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_eq_one_add : B₃ R = 1 + N₃ R := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [B₃, N₃] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq : (N₁ R) ^ 2 = !![0, 0, 0; 0, -4, 4; 0, -4, 4] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_cube : (N₁ R) ^ 3 = 0 := by
  rw [pow_succ, PadicBerggren.N₁_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₁, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₃_sq : (N₃ R) ^ 2 = !![-4, 0, 4; 0, 0, 0; -4, 0, 4] := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₃, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₃_cube : (N₃ R) ^ 3 = 0 := by
  rw [pow_succ, PadicBerggren.N₃_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [N₃, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq_ne_zero (h4 : (4 : R) ≠ 0) : (N₁ R) ^ 2 ≠ 0 := by
  intro h
  rw [PadicBerggren.N₁_sq] at h
  have := congrFun (congrFun h 1) 2
  simp at this
  exact h4 (by linear_combination this)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem N₁_sq_eq_zero_of_four_eq_zero (h4 : (4 : R) = 0) : (N₁ R) ^ 2 = 0 := by
  rw [PadicBerggren.N₁_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h4]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem pow_unipotent_formula {S : Type*} [Ring S] (X : S) (hX : X ^ 3 = 0) (n : ℕ) :
    (1 + X) ^ n = 1 + (n : S) * X + ((n.choose 2 : ℕ) : S) * X ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hc : (((n + 1).choose 2 : ℕ) : S) = ((n.choose 2 : ℕ) : S) + (n : S) := by
        rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]
        push_cast
        exact add_comm _ _
      have expand : (1 + (n : S) * X + ((n.choose 2 : ℕ) : S) * X ^ 2) * (1 + X)
          = (1 + ((n : S) + 1) * X + (((n.choose 2 : ℕ) : S) + (n : S)) * X ^ 2)
            + ((n.choose 2 : ℕ) : S) * X ^ 3 := by
        noncomm_ring
      rw [pow_succ, ih, expand, hX, mul_zero, add_zero]
      push_cast [hc]
      noncomm_ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem natCast_matrix_mul {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (M : Matrix n n R) : ((m : Matrix n n R)) * M = (m : R) • M := by
  have h : ((m : ℕ) : Matrix n n R) = (m : R) • (1 : Matrix n n R) := by
    ext i j
    simp [Matrix.natCast_apply, Matrix.one_apply, apply_ite ((↑) : ℕ → R)]
  rw [h, Matrix.smul_mul, one_mul]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

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

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem choose_two_cast_eq_zero (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (((p ^ k).choose 2 : ℕ) : ZMod (p ^ k)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact PadicBerggren.pow_dvd_choose_two p k hp hodd

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_pow_p_pow (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₁ (ZMod (p ^ k))) ^ (p ^ k) = 1 := by
  have hpk : ((p ^ k : ℕ) : ZMod (p ^ k)) = 0 := ZMod.natCast_self _
  have hchoose := PadicBerggren.choose_two_cast_eq_zero p k hp hodd
  rw [PadicBerggren.B₁_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₁_cube]
  rw [natCast_matrix_eq_zero _ hpk, natCast_matrix_eq_zero _ hchoose]
  simp

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_pow_p_pow (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₃ (ZMod (p ^ k))) ^ (p ^ k) = 1 := by
  have hpk : ((p ^ k : ℕ) : ZMod (p ^ k)) = 0 := ZMod.natCast_self _
  have hchoose := PadicBerggren.choose_two_cast_eq_zero p k hp hodd
  rw [PadicBerggren.B₃_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₃_cube]
  rw [natCast_matrix_eq_zero _ hpk, natCast_matrix_eq_zero _ hchoose]
  simp

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_order_exact (p k m : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (h : (B₁ (ZMod (p ^ k))) ^ m = 1) : p ^ k ∣ m := by
  rw [PadicBerggren.B₁_eq_one_add, PadicBerggren.pow_unipotent_formula _ PadicBerggren.N₁_cube] at h
  have h01 := congrFun (congrFun h 0) 1
  rw [PadicBerggren.natCast_matrix_mul, PadicBerggren.natCast_matrix_mul, PadicBerggren.N₁_sq] at h01
  simp [Matrix.add_apply, N₁] at h01
  -- `h01 : (m : ZMod (p^k)) * (-2) = 0` up to normalisation
  have h2 : ((2 * m : ℕ) : ZMod (p ^ k)) = 0 := by
    push_cast
    linear_combination h01
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hodd)
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop h2)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_pow_ne_one_padic (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    (B₁ (ZMod (p ^ (k + 1)))) ^ (p ^ k) ≠ 1 := by
  intro h
  have hdvd := PadicBerggren.B₁_order_exact p (k + 1) (p ^ k) hp hodd h
  have hle := Nat.le_of_dvd (Nat.pow_pos hp.pos) hdvd
  have hlt : p ^ k < p ^ (k + 1) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_fixes_null_line : B₁ R *ᵥ ![0, 1, 1] = ![0, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₁_fixed_vector : lorentz R ![0, 1, 1] = 0 := by
  simp [lorentz]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₃_fixes_null_line : B₃ R *ᵥ ![1, 0, 1] = ![1, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_B₃_fixed_vector : lorentz R ![1, 0, 1] = 0 := by
  simp [lorentz]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_fixed_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (v : Fin 3 → ZMod p) :
    B₁ (ZMod p) *ᵥ v = v ↔ v = ![0, v 1, v 1] := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    have hv2 : v 2 = v 1 := by
      have : (2 : ZMod p) * (v 2 - v 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · linear_combination h
    have hv0 : v 0 = 0 := by
      have : (2 : ZMod p) * v 0 = 0 := by linear_combination h1 - 2 * hv2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2
      · exact h
    funext i
    fin_cases i <;> simp [hv0, hv2]
  · intro h
    rw [h]
    funext i
    fin_cases i <;>
      simp [B₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_eq (c : R) : scal2 c = !![c, 0; 0, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scal2]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_mul (a b : R) : scal2 a * scal2 b = scal2 (a * b) := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_pow (a : R) (n : ℕ) : (scal2 a) ^ n = scal2 (a ^ n) := by
  induction n with
  | zero => simp [scal2]
  | succ n ih => rw [pow_succ, ih, PadicBerggren.scal2_mul, pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem scal2_commute (a : R) (M : Matrix (Fin 2) (Fin 2) R) : Commute (scal2 a) M := by
  unfold Commute SemiconjBy scal2
  rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_decomp : Um R = scal2 (3 : R) + scal2 (2 : R) * Jm R := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Um, Jm]; try ring)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Jm_sq : (Jm R) ^ 2 = scal2 (2 : R) := by
  rw [pow_two]
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_mul_inv : Um R * !![3, -2; -4, 3] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_conj_mul : (scal2 (3 : R) + scal2 (-2 : R) * Jm R) * Um R = 1 := by
  simp only [PadicBerggren.scal2_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Jm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_one : emb (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_mul (A B : Matrix (Fin 2) (Fin 2) R) : emb (A * B) = emb A * emb B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem emb_pow (A : Matrix (Fin 2) (Fin 2) R) (n : ℕ) : emb (A ^ n) = (emb A) ^ n := by
  induction n with
  | zero => simpa using PadicBerggren.emb_one (R := R)
  | succ n ih => rw [pow_succ, PadicBerggren.emb_mul, ih, pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_sq : (Sm R) ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_pow_even {m : ℕ} (hm : Even m) : (Sm R) ^ m = 1 := by
  obtain ⟨t, ht⟩ := hm
  rw [show m = 2 * t by omega, pow_mul, PadicBerggren.Sm_sq, one_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Sm_commute_emb_Um : Commute (Sm R) (emb (Um R)) := by
  unfold Commute SemiconjBy
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_mul_Wm : B₂ R * Wm R = Wm R * (Sm R * emb (Um R)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B₂, Wm, Sm, emb, Um, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Wm_mul_Vm : (Wm R) * Vm R = (2 : R) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wm, Vm, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_mul_Wm (n : ℕ) : (B₂ R) ^ n * Wm R = Wm R * (Sm R * emb (Um R)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_assoc, PadicBerggren.B₂_mul_Wm, ← mul_assoc, ih, mul_assoc, ← pow_succ]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_eq_one_of_block (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {m : ℕ}
    (hU : (Um (ZMod p)) ^ m = 1) (hm : Even m) : (B₂ (ZMod p)) ^ m = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h')
  have hblock : (Sm (ZMod p) * emb (Um (ZMod p))) ^ m = 1 := by
    rw [Commute.mul_pow PadicBerggren.Sm_commute_emb_Um, PadicBerggren.Sm_pow_even hm, ← PadicBerggren.emb_pow, hU, PadicBerggren.emb_one, one_mul]
  have key : (B₂ (ZMod p)) ^ m * Wm (ZMod p) = Wm (ZMod p) := by
    rw [PadicBerggren.B₂_pow_mul_Wm, hblock, mul_one]
  have key2 : (B₂ (ZMod p)) ^ m * ((2 : ZMod p) • 1) = (2 : ZMod p) • 1 := by
    rw [← PadicBerggren.Wm_mul_Vm, ← mul_assoc, key]
  rw [Matrix.mul_smul, mul_one] at key2
  ext i j
  have := congrFun (congrFun key2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ h2 this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Jm_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Jm (ZMod p)) ^ p = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have hp' : p = 2 * (p / 2) + 1 := by omega
  calc (Jm (ZMod p)) ^ p = ((Jm (ZMod p)) ^ 2) ^ (p / 2) * Jm (ZMod p) := by
        rw [← pow_mul, ← pow_succ]; exact congrArg _ hp'
    _ = scal2 ((2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by rw [PadicBerggren.Jm_sq, PadicBerggren.scal2_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem Um_pow_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Um (ZMod p)) ^ p
      = scal2 (3 : ZMod p) + scal2 (2 * (2 : ZMod p) ^ (p / 2)) * Jm (ZMod p) := by
  have hcomm : Commute (scal2 (3 : ZMod p)) (scal2 (2 : ZMod p) * Jm (ZMod p)) :=
    scal2_commute _ _
  rw [PadicBerggren.Um_decomp, add_pow_char_of_commute p hcomm,
    Commute.mul_pow (scal2_commute (2 : ZMod p) (Jm (ZMod p))), PadicBerggren.scal2_pow, PadicBerggren.scal2_pow,
    Jm_pow_card p hp, ZMod.pow_card, ZMod.pow_card, ← mul_assoc, PadicBerggren.scal2_mul]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

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

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_p_sub_one_of_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
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
    rw [PadicBerggren.Um_pow_card p hp, heps, mul_one, ← PadicBerggren.Um_decomp]
  have hU : (Um (ZMod p)) ^ (p - 1) = 1 := by
    have hsplit : (Um (ZMod p)) ^ p = (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) := by
      rw [← pow_succ]
      congr 1
      omega
    have : (Um (ZMod p)) ^ (p - 1) * Um (ZMod p) = Um (ZMod p) := by rw [← hsplit, hUp]
    calc (Um (ZMod p)) ^ (p - 1)
        = (Um (ZMod p)) ^ (p - 1) * (Um (ZMod p) * !![3, -2; -4, 3]) := by
          rw [PadicBerggren.Um_mul_inv, mul_one]
      _ = ((Um (ZMod p)) ^ (p - 1) * Um (ZMod p)) * !![3, -2; -4, 3] := by rw [mul_assoc]
      _ = Um (ZMod p) * !![3, -2; -4, 3] := by rw [this]
      _ = 1 := PadicBerggren.Um_mul_inv
  refine PadicBerggren.B₂_pow_eq_one_of_block p hp hU ?_
  exact (Nat.even_sub (by omega)).mpr (by simp [Nat.not_even_iff.mpr hmod])

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_p_add_one_of_not_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (h : ¬ IsSquare (2 : ZMod p)) : (B₂ (ZMod p)) ^ (p + 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hmod : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hpp).resolve_left hp
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have heps : (2 : ZMod p) ^ (p / 2) = -1 := by
    rcases PadicBerggren.two_pow_div_two_eq p hp with h1 | h1
    · exact absurd ((ZMod.euler_criterion p h2).mpr h1) h
    · exact h1
  have hU : (Um (ZMod p)) ^ (p + 1) = 1 := by
    rw [pow_succ, PadicBerggren.Um_pow_card p hp, heps]
    have : (2 : ZMod p) * (-1) = -2 := by ring
    rw [this]
    exact PadicBerggren.Um_conj_mul
  refine PadicBerggren.B₂_pow_eq_one_of_block p hp hU ?_
  exact Nat.even_add_one.mpr (Nat.not_even_iff.mpr hmod)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_card_sq_sub_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (B₂ (ZMod p)) ^ (p ^ 2 - 1) = 1 := by
  have hpp : p.Prime := Fact.out
  have hp1 : 1 ≤ p := hpp.one_lt.le.trans' (by omega)
  have hfac : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have := Nat.sq_sub_sq p 1
    simpa using this
  by_cases h : IsSquare (2 : ZMod p)
  · rw [hfac, mul_comm, pow_mul, PadicBerggren.B₂_pow_p_sub_one_of_isSquare_two p hp h, one_pow]
  · rw [hfac, pow_mul, PadicBerggren.B₂_pow_p_add_one_of_not_isSquare_two p hp h, one_pow]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_orderOf_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    orderOf (B₂ (ZMod p)) ∣ p ^ 2 - 1 :=
  orderOf_dvd_of_pow_eq_one (PadicBerggren.B₂_pow_card_sq_sub_one p hp)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_no_nonzero_fixed_point (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ZMod p) (h : B₂ (ZMod p) *ᵥ v = v) : v = 0 := by
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2' := congrFun h 2
  simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2'
  have e0 : (2 : ZMod p) * (v 1 + v 2) = 0 := by linear_combination h0
  have e1 : (2 : ZMod p) * (v 0 + v 2) = 0 := by linear_combination h1
  have e2 : (2 : ZMod p) * (v 0 + v 1 + v 2) = 0 := by linear_combination h2'
  have f0 : v 1 + v 2 = 0 := by
    rcases mul_eq_zero.mp e0 with hh | hh
    · exact absurd hh h2
    · exact hh
  have f1 : v 0 + v 2 = 0 := by
    rcases mul_eq_zero.mp e1 with hh | hh
    · exact absurd hh h2
    · exact hh
  have f2 : v 0 + v 1 + v 2 = 0 := by
    rcases mul_eq_zero.mp e2 with hh | hh
    · exact absurd hh h2
    · exact hh
  have hv2 : v 2 = 0 := by linear_combination f0 + f1 - f2
  have hv1 : v 1 = 0 := by linear_combination f0 - hv2
  have hv0 : v 0 = 0 := by linear_combination f1 - hv2
  funext i
  fin_cases i <;> simp [hv0, hv1, hv2]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_null_eigenvector_iff_isSquare_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ (lam : ZMod p) (v : Fin 3 → ZMod p), v ≠ 0 ∧ lorentz (ZMod p) v = 0 ∧
      B₂ (ZMod p) *ᵥ v = lam • v) ↔ IsSquare (2 : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hh
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  constructor
  · rintro ⟨lam, v, hv0, hvnull, hveq⟩
    have hker : (B₂ (ZMod p) - lam • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hveq]
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]
    have hdet : (B₂ (ZMod p) - lam • (1 : Matrix (Fin 3) (Fin 3) (ZMod p))).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hker⟩
    have hpoly : (lam + 1) * (lam ^ 2 - 6 * lam + 1) = 0 := by
      rw [Matrix.det_fin_three] at hdet
      simp [B₂, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hdet
      linear_combination -hdet
    rcases mul_eq_zero.mp hpoly with hlam | hlam
    · -- eigenvalue −1: its eigenline `(t,−t,0)` is not null
      exfalso
      have hlam' : lam = -1 := by linear_combination hlam
      subst hlam'
      have h0 := congrFun hveq 0
      have h1 := congrFun hveq 1
      have h2' := congrFun hveq 2
      simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2'
      have e2 : (2 : ZMod p) * v 2 = 0 := by linear_combination h2' - h0
      have hv2 : v 2 = 0 := by
        rcases mul_eq_zero.mp e2 with hh | hh
        · exact absurd hh h2
        · exact hh
      have esum : (2 : ZMod p) * (v 0 + v 1) = 0 := by linear_combination h0 - 2 * hv2
      have hsum : v 0 + v 1 = 0 := by
        rcases mul_eq_zero.mp esum with hh | hh
        · exact absurd hh h2
        · exact hh
      have hv1 : v 1 = -v 0 := by linear_combination hsum
      have hnull : (2 : ZMod p) * (v 0 * v 0) = 0 := by
        simp [lorentz, hv1, hv2] at hvnull
        linear_combination hvnull
      have hv0' : v 0 = 0 := by
        rcases mul_eq_zero.mp hnull with hh | hh
        · exact absurd hh h2
        · exact (mul_self_eq_zero.mp hh)
      apply hv0
      funext i
      fin_cases i <;> simp [hv0', hv1, hv2]
    · -- eigenvalue 3 ± 2√2 forces 2 to be a square
      refine ⟨(lam - 3) / 2, ?_⟩
      field_simp
      linear_combination -hlam
  · rintro ⟨s, hs⟩
    refine ⟨3 + 2 * s, ![1, 1, s], ?_, ?_, ?_⟩
    · intro hcon
      have := congrFun hcon 0
      simp at this
    · simp [lorentz]
      linear_combination hs
    · funext i
      fin_cases i <;>
        simp [B₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
        first
          | ring1
          | linear_combination (2 : ZMod p) * hs

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_null_eigenvector_iff_mod_eight (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∃ (lam : ZMod p) (v : Fin 3 → ZMod p), v ≠ 0 ∧ lorentz (ZMod p) v = 0 ∧
      B₂ (ZMod p) *ᵥ v = lam • v) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  (PadicBerggren.B₂_null_eigenvector_iff_isSquare_two p hp).trans (ZMod.exists_sq_eq_two_iff hp)

end

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mono {d e : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (h : d ∣ e) (hA : EntryDvd e A) :
    EntryDvd d A := fun i j => h.trans (hA i j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem add {d : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A) (hB : EntryDvd d B) :
    EntryDvd d (A + B) := fun i j => by
  simpa [Matrix.add_apply] using dvd_add (hA i j) (hB i j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mul {d e : ℤ} {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (hB : EntryDvd e B) : EntryDvd (d * e) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => mul_dvd_mul (hA i k) (hB k j)

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

namespace EntryDvd

section
variable {R : Type*} [CommRing R]

theorem mul_right {d : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : EntryDvd d A)
    (B : Matrix (Fin 3) (Fin 3) ℤ) : EntryDvd d (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (hA i k) _

end

end EntryDvd

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem entryDvd_mulVec {d : ℤ} {A : Matrix (Fin 3) (Fin 3) ℤ} (h : EntryDvd d A)
    (v : Fin 3 → ℤ) (i : Fin 3) : d ∣ (A *ᵥ v) i := by
  have hsum : (A *ᵥ v) i = ∑ j : Fin 3, A i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hsum]
  exact Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (h i j) _

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem pow_one_add_eq {S : Type*} [Ring S] (X : S) (n : ℕ) :
    ∃ C : S, (1 + X) ^ n = 1 + (n : S) * X + X ^ 2 * C := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨C + (n : S) + C * X, ?_⟩
      have hcom : (n : S) * X * X = X ^ 2 * (n : S) := by
        rw [mul_assoc, ← pow_two]
        exact (Nat.cast_commute n (X ^ 2)).eq
      have expand : (1 + (n : S) * X + X ^ 2 * C) * (1 + X)
          = (1 + ((n : S) + 1) * X + X ^ 2 * (C + (n : S) + C * X))
            + ((n : S) * X * X - X ^ 2 * (n : S)) := by
        noncomm_ring
      rw [pow_succ, hC, expand, hcom]
      push_cast
      noncomm_ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem natCast_matrix_mul_int (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ((m : Matrix (Fin 3) (Fin 3) ℤ)) * M = (m : ℤ) • M := PadicBerggren.natCast_matrix_mul m M

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lift_step (A : Matrix (Fin 3) (Fin 3) ℤ) (p j : ℕ) (hj : 1 ≤ j)
    (h : EntryDvd ((p : ℤ) ^ j) (A - 1)) : EntryDvd ((p : ℤ) ^ (j + 1)) (A ^ p - 1) := by
  obtain ⟨C, hC⟩ := PadicBerggren.pow_one_add_eq (A - 1) p
  have hA : (1 : Matrix (Fin 3) (Fin 3) ℤ) + (A - 1) = A := by
    rw [add_sub_cancel]
  rw [hA] at hC
  have hsplit : A ^ p - 1
      = (p : Matrix (Fin 3) (Fin 3) ℤ) * (A - 1) + (A - 1) ^ 2 * C := by
    rw [hC]
    noncomm_ring
  rw [hsplit]
  refine EntryDvd.add ?_ ?_
  · rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j'
    rw [Matrix.smul_apply, smul_eq_mul, pow_succ']
    exact mul_dvd_mul_left _ (h i j')
  · have hsq : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2) := by
      rw [pow_two]
      exact h.mul h
    have hprod : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2 * C) := hsq.mul_right C
    refine EntryDvd.mono ?_ hprod
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega)

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lift_pow (A : Matrix (Fin 3) (Fin 3) ℤ) (p : ℕ) (h : EntryDvd (p : ℤ) (A - 1))
    (k : ℕ) : EntryDvd ((p : ℤ) ^ (k + 1)) (A ^ (p ^ k) - 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hstep := PadicBerggren.lift_step (A ^ (p ^ k)) p (k + 1) (by omega) ih
      rwa [← pow_mul, ← pow_succ] at hstep

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem redRing_B₂ (m : ℕ) : redRing m (B₂ ℤ) = B₂ (ZMod m) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redRing, RingHom.mapMatrix_apply, B₂]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem entryDvd_iff_red (m : ℕ) (A : Matrix (Fin 3) (Fin 3) ℤ) :
    EntryDvd (m : ℤ) A ↔ redRing m A = 0 := by
  constructor
  · intro h
    ext i j
    simpa [redRing, RingHom.mapMatrix_apply] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd (A i j) m).mpr (h i j)
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [redRing, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Int.coe_castRingHom] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (A i j) m).mp this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_int_pow_sub_one_dvd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    EntryDvd (p : ℤ) ((B₂ ℤ) ^ (p ^ 2 - 1) - 1) := by
  rw [PadicBerggren.entryDvd_iff_red]
  rw [map_sub, map_pow, map_one, PadicBerggren.redRing_B₂, PadicBerggren.B₂_pow_card_sq_sub_one p hp, sub_self]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_pow_eq_one_padic (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (B₂ (ZMod (p ^ (k + 1)))) ^ ((p ^ 2 - 1) * p ^ k) = 1 := by
  have hlift := PadicBerggren.lift_pow ((B₂ ℤ) ^ (p ^ 2 - 1)) p (PadicBerggren.B₂_int_pow_sub_one_dvd p hp) k
  rw [← pow_mul] at hlift
  have hcast : ((p : ℤ) ^ (k + 1)) = ((p ^ (k + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, PadicBerggren.entryDvd_iff_red] at hlift
  rw [map_sub, map_pow, map_one, PadicBerggren.redRing_B₂] at hlift
  have := sub_eq_zero.mp hlift
  exact this

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_padic_contraction (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ℤ) (i : Fin 3) :
    ((p : ℤ) ^ (k + 1)) ∣ (((B₂ ℤ) ^ ((p ^ 2 - 1) * p ^ k)) *ᵥ v) i - v i := by
  have hlift := PadicBerggren.lift_pow ((B₂ ℤ) ^ (p ^ 2 - 1)) p (PadicBerggren.B₂_int_pow_sub_one_dvd p hp) k
  rw [← pow_mul] at hlift
  have key := PadicBerggren.entryDvd_mulVec hlift v i
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at key

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_int_pow_sub_one (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
    EntryDvd ((p : ℤ) ^ k) ((B₁ ℤ) ^ (p ^ k) - 1) := by
  have hform := PadicBerggren.pow_unipotent_formula (N₁ ℤ) PadicBerggren.N₁_cube (p ^ k)
  rw [← PadicBerggren.B₁_eq_one_add] at hform
  have hsub : (B₁ ℤ) ^ (p ^ k) - 1
      = ((p ^ k : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * N₁ ℤ
        + (((p ^ k).choose 2 : ℕ) : Matrix (Fin 3) (Fin 3) ℤ) * (N₁ ℤ) ^ 2 := by
    rw [hform]
    noncomm_ring
  rw [hsub]
  refine EntryDvd.add ?_ ?_
  · rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j
    refine ⟨(N₁ ℤ) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  · obtain ⟨t, ht⟩ := PadicBerggren.pow_dvd_choose_two p k hp hodd
    rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j
    refine ⟨(t : ℤ) * ((N₁ ℤ) ^ 2) i j, ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, ht]
    push_cast
    ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_padic_contraction (p k : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (v : Fin 3 → ℤ) (i : Fin 3) :
    ((p : ℤ) ^ k) ∣ (((B₁ ℤ) ^ (p ^ k)) *ᵥ v) i - v i := by
  have key := PadicBerggren.entryDvd_mulVec (PadicBerggren.B₁_int_pow_sub_one p k hp hodd) v i
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at key

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₁_B₂_noncommute (p : ℕ) [hp' : Fact p.Prime] (hp : p ≠ 2) :
    B₁ (ZMod p) * B₂ (ZMod p) ≠ B₂ (ZMod p) * B₁ (ZMod p) := by
  intro h
  have h00 : (B₁ (ZMod p) * B₂ (ZMod p)) 0 0 = (B₂ (ZMod p) * B₁ (ZMod p)) 0 0 := by rw [h]
  have e1 : (B₁ (ZMod p) * B₂ (ZMod p)) 0 0 = 1 := by
    simp [B₁, B₂, Matrix.mul_apply, Fin.sum_univ_three]
  have e2 : (B₂ (ZMod p) * B₁ (ZMod p)) 0 0 = 9 := by
    simp [B₂, B₁, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num
  rw [e1, e2] at h00
  have h8 : ((8 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination -h00
  have hdvd : p ∣ 8 := (ZMod.natCast_eq_zero_iff _ _).mp h8
  have hdvd2 : p ∣ 2 ^ 3 := by simpa using hdvd
  exact hp ((Nat.prime_dvd_prime_iff_eq hp'.out Nat.prime_two).mp
    (hp'.out.dvd_of_dvd_pow hdvd2))

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem B₂_orbit_periodic (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (v : Fin 3 → ZMod (p ^ (k + 1))) :
    (B₂ (ZMod (p ^ (k + 1)))) ^ ((p ^ 2 - 1) * p ^ k) *ᵥ v = v := by
  rw [PadicBerggren.B₂_pow_eq_one_padic p k hp, Matrix.one_mulVec]

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_root : lorentz R (root R) = 0 := by
  simp [lorentz, root]
  ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_gen (i : Fin 3) (v : Fin 3 → R) : lorentz R (gen R i *ᵥ v) = lorentz R v := by
  fin_cases i <;>
    simp [gen, lorentz, B₁, B₂, B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem lorentz_wordMat (w : List (Fin 3)) :
    lorentz R (wordMat R w *ᵥ root R) = 0 := by
  induction w with
  | nil => simpa [wordMat, Matrix.one_mulVec] using PadicBerggren.lorentz_root (R := R)
  | cons a w ih =>
      have hstep : wordMat R (a :: w) *ᵥ root R = gen R a *ᵥ (wordMat R w *ᵥ root R) := by
        simp [wordMat, List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]
      rw [hstep, PadicBerggren.lorentz_gen]
      exact ih

end

end PadicBerggren

namespace PadicBerggren

section
variable {R : Type*} [CommRing R]

theorem tree_collision_mod (m d : ℕ) [NeZero m] (h : m ^ 3 < 3 ^ d) :
    ∃ w₁ w₂ : Fin d → Fin 3, w₁ ≠ w₂ ∧
      wordMat (ZMod m) (List.ofFn w₁) *ᵥ root (ZMod m)
        = wordMat (ZMod m) (List.ofFn w₂) *ᵥ root (ZMod m) := by
  have hcard : Fintype.card (Fin 3 → ZMod m) < Fintype.card (Fin d → Fin 3) := by
    simpa [Fintype.card_fun, ZMod.card] using h
  obtain ⟨w₁, w₂, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun w : Fin d → Fin 3 => wordMat (ZMod m) (List.ofFn w) *ᵥ root (ZMod m)) hcard
  exact ⟨w₁, w₂, hne, heq⟩

end

end PadicBerggren


theorem solution (A : Matrix (Fin 3) (Fin 3) ℤ) (p j : ℕ) (hj : 1 ≤ j)
    (h : EntryDvd ((p : ℤ) ^ j) (A - 1)) : EntryDvd ((p : ℤ) ^ (j + 1)) (A ^ p - 1) := by
  obtain ⟨C, hC⟩ := PadicBerggren.pow_one_add_eq (A - 1) p
  have hA : (1 : Matrix (Fin 3) (Fin 3) ℤ) + (A - 1) = A := by
    rw [add_sub_cancel]
  rw [hA] at hC
  have hsplit : A ^ p - 1
      = (p : Matrix (Fin 3) (Fin 3) ℤ) * (A - 1) + (A - 1) ^ 2 * C := by
    rw [hC]
    noncomm_ring
  rw [hsplit]
  refine EntryDvd.add ?_ ?_
  · rw [PadicBerggren.natCast_matrix_mul_int]
    intro i j'
    rw [Matrix.smul_apply, smul_eq_mul, pow_succ']
    exact mul_dvd_mul_left _ (h i j')
  · have hsq : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2) := by
      rw [pow_two]
      exact h.mul h
    have hprod : EntryDvd ((p : ℤ) ^ j * (p : ℤ) ^ j) ((A - 1) ^ 2 * C) := hsq.mul_right C
    refine EntryDvd.mono ?_ hprod
    rw [← pow_add]
    exact pow_dvd_pow _ (by omega)

#print axioms solution
