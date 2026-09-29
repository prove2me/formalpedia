-- Prove2me | solution 1 for PadicBerggren.B2_null_eigenvector_iff_isSquare_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T22:58:40.398704+00:00
-- url     : https://prove2.me/submissions/1bb7d13e-950f-41f9-9795-7cdb0e2fa24d

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
theorem solution(p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
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
