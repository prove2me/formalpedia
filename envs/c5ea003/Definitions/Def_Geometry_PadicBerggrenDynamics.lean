-- Prove2me | Definitions.Def_Geometry_PadicBerggrenDynamics
-- name    : Geometry_PadicBerggrenDynamics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:35.289827+00:00
-- url     : https://prove2.me/theorems/1d5e159b-1c83-4fc9-86ac-6d697a5089b7
-- title:
--   Aether Catalog definitions — Geometry_PadicBerggrenDynamics
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PadicBerggrenDynamics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PadicBerggrenDynamics.lean by skeleton subtraction
import Mathlib
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

namespace PadicBerggren

open Matrix

/-! ## The generators and the Lorentz form -/

section Defs
variable (R : Type*) [CommRing R]

/-- First Berggren generator (unipotent). -/
def B₁ : Matrix (Fin 3) (Fin 3) R := !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Second Berggren generator (hyperbolic). -/
def B₂ : Matrix (Fin 3) (Fin 3) R := !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Third Berggren generator (unipotent). -/
def B₃ : Matrix (Fin 3) (Fin 3) R := !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- Inverse of `B₁`. -/
def C₁ : Matrix (Fin 3) (Fin 3) R := !![1, 2, -2; -2, -1, 2; -2, -2, 3]

/-- Inverse of `B₂`. -/
def C₂ : Matrix (Fin 3) (Fin 3) R := !![1, 2, -2; 2, 1, -2; -2, -2, 3]

/-- Inverse of `B₃`. -/
def C₃ : Matrix (Fin 3) (Fin 3) R := !![-1, -2, 2; 2, 1, -2; -2, -2, 3]

/-- The Lorentz form `a² + b² − c²` preserved by the Berggren moves. -/
def lorentz (v : Fin 3 → R) : R := v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2

/-- The null cone of the Lorentz form: the "Pythagorean" locus mod `p^k`. -/
def nullCone : Set (Fin 3 → R) := {v | lorentz R v = 0}

/-- The nilpotent part of `B₁`. -/
def N₁ : Matrix (Fin 3) (Fin 3) R := !![0, -2, 2; 2, -2, 2; 2, -2, 2]

/-- The nilpotent part of `B₃`. -/
def N₃ : Matrix (Fin 3) (Fin 3) R := !![-2, 2, 2; -2, 0, 2; -2, 2, 2]

end Defs

variable {R : Type*} [CommRing R]







/-! ### Determinants and inverses -/










/-! ### The moves are bijections of the null cone

Over `ZMod (p^k)` the null cone is a finite set, so each Berggren move becomes a permutation
of a finite set: the tree reduces to an invertible finite dynamical system. -/





/-! ## Unipotent generators -/










/-! ### Order of the unipotent generators mod `p^k` -/


theorem natCast_matrix_eq_zero {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (h : (m : R) = 0) : ((m : ℕ) : Matrix n n R) = 0 := by
  ext i j
  simp [Matrix.natCast_apply, apply_ite ((↑) : ℕ → R), h]







/-! ### The unipotent generators fix a single null line -/






/-! ## The hyperbolic generator

`B₂` is conjugate (over `ℤ[1/2]`) to `diag(−1) ⊕ U` with `U = !![3,2;4,3]`, the matrix of
multiplication by the square `3 + 2√2` of the silver ratio on `ℤ[√2]`.  We prove everything
through the concrete conjugation `B₂ · W = W · (S · emb U)`. -/

/-- The hyperbolic `2×2` block. -/
def Um (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![3, 2; 4, 3]

/-- The "`√2`" matrix: `J² = 2`. -/
def Jm (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 2, 0]

/-- Scalar `2×2` matrices. -/
def scal2 (c : R) : Matrix (Fin 2) (Fin 2) R := c • (1 : Matrix (Fin 2) (Fin 2) R)









/-- Block embedding `2×2 ↪ 3×3` (identity on the first coordinate). -/
def emb (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]




/-- The sign block carrying the `−1` eigenvalue of `B₂`. -/
def Sm (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![-1, 0, 0; 0, 1, 0; 0, 0, 1]

/-- Conjugating matrix: its columns are the eigenvectors `(1,−1,0)`, `(1,1,0)`, `(0,0,1)`. -/
def Wm (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![1, 1, 0; -1, 1, 0; 0, 0, 1]

/-- `2 · Wm⁻¹`, an integral matrix. -/
def Vm (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![1, -1, 0; 1, 1, 0; 0, 0, 2]








/-! ### Frobenius on the hyperbolic block -/

instance matrixCharP (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] (p : ℕ)
    [Fact p.Prime] : CharP (Matrix n n (ZMod p)) p := by
  constructor
  intro m
  constructor
  · intro h
    have h0 : ((m : ℕ) : ZMod p) = 0 := by
      have := congrFun (congrFun h (Classical.arbitrary n)) (Classical.arbitrary n)
      simpa [Matrix.natCast_apply] using this
    exact (ZMod.natCast_eq_zero_iff m p).mp h0
  · intro h
    have h0 : ((m : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr h
    exact natCast_matrix_eq_zero _ h0








/-! ### Fixed points and the split/inert dichotomy on the null cone -/




/-! ## Depth: lifting from `ZMod p` to `ZMod (p^k)` -/

/-- Entrywise divisibility of an integer matrix. -/
def EntryDvd (d : ℤ) (A : Matrix (Fin 3) (Fin 3) ℤ) : Prop := ∀ i j, d ∣ A i j

namespace EntryDvd





end EntryDvd






/-- Reduction of an integer matrix mod `m`. -/
def redRing (m : ℕ) : Matrix (Fin 3) (Fin 3) ℤ →+* Matrix (Fin 3) (Fin 3) (ZMod m) :=
  (Int.castRingHom (ZMod m)).mapMatrix










/-! ## The boundary of the tree does not survive reduction

The Berggren tree is a ternary tree: `3^d` vertices at depth `d`.  Reducing mod `m` lands in a
set of size `m³`, so the reduction map on words is massively non-injective; the "boundary at
infinity" cannot be embedded in a fixed finite level `ZMod (p^k)`.  (What does survive is the
inverse-limit statement `B₂_padic_contraction`.) -/

/-- The three generators indexed by `Fin 3`. -/
def gen (R : Type*) [CommRing R] (i : Fin 3) : Matrix (Fin 3) (Fin 3) R :=
  ![B₁ R, B₂ R, B₃ R] i

/-- The matrix attached to a word in the generators. -/
def wordMat (R : Type*) [CommRing R] (w : List (Fin 3)) : Matrix (Fin 3) (Fin 3) R :=
  (w.map (gen R)).prod

/-- The root of the tree, the triple `(3,4,5)`. -/
def root (R : Type*) [CommRing R] : Fin 3 → R := ![3, 4, 5]





end PadicBerggren


