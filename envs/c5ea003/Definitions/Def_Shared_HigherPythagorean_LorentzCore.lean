-- Prove2me | Definitions.Def_Shared_HigherPythagorean_LorentzCore
-- name    : Shared_HigherPythagorean_LorentzCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:54:15.273442+00:00
-- url     : https://prove2.me/theorems/91331fa4-206d-4081-ba7d-55a1eb9b4956
-- title:
--   Aether Catalog definitions — Shared_HigherPythagorean_LorentzCore
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HigherPythagorean.LorentzCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HigherPythagorean/LorentzCore.lean by skeleton subtraction
import Mathlib

/-!
# The Lorentz form of signature `(n,1)`, its integral automorphisms, and the reflection move

This file sets up the general framework in which the Berggren tree of primitive Pythagorean
triples and its higher–dimensional analogues live:

* `lorentzJ n`   — the Gram matrix `diag(1,…,1,-1)` of the form `x₁²+…+xₙ² − y²`;
* `lorentzQ n v` — the form itself;
* `NullCone n`   — its integral null cone (`= ` Pythagorean `n`-tuples);
* `IsIntegralLorentz n M` — the integral automorphisms of the form.

Main results.

* `lorentzQ_mulVec` : integral Lorentz matrices preserve the form, hence the null cone
  (`IsIntegralLorentz.mapsTo_nullCone`).
* `IsIntegralLorentz.det_sq` : such matrices have determinant `±1`.
* `lorentz_move_height_bound` : the *sharp* growth constant of the reflection move in the
  all-ones vector: the height is multiplied by at most `(√n+1)/(√n−1)`.  For `n = 2` this is
  `3+2√2 = (1+√2)²`, the square of the silver ratio (Berggren); for `n = 3` it is `2+√3`.
* `refl_not_integral_of_four_le` : the all-ones reflection is *not* integral for `n ≥ 4`,
  so the Berggren mechanism only exists in dimensions `n = 2, 3`.
-/

namespace HigherPythagorean

open Matrix Finset

section Form

variable (n : ℕ)

/-- Gram matrix of the Lorentz form of signature `(n,1)`: `diag(1,…,1,-1)`. -/
def lorentzJ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.diagonal fun i => if i = Fin.last n then -1 else 1

/-- The Lorentz quadratic form `q(v) = v ⬝ J ⬝ v = x₁²+…+xₙ² − y²`. -/
def lorentzQ (v : Fin (n + 1) → ℤ) : ℤ := v ⬝ᵥ (lorentzJ n *ᵥ v)

/-- The integral null cone of the Lorentz form: solutions of `x₁²+…+xₙ² = y²`. -/
def NullCone : Set (Fin (n + 1) → ℤ) := {v | lorentzQ n v = 0}

variable {n}




end Form

section Automorphisms

variable {n : ℕ}

/-- An integral automorphism of the Lorentz form: `Mᵀ J M = J`. -/
def IsIntegralLorentz (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) : Prop :=
  Mᵀ * lorentzJ n * M = lorentzJ n







end Automorphisms

section Reflection

/-!
### The all-ones reflection and its growth constant

For the vector `r = (1,…,1;1)` one has `q(r) = n − 1` and the reflection
`s_r(v) = v − (2·B(v,r)/(n−1))·r` subtracts the *same* rational number from every coordinate.
Its effect on the height (last coordinate) is `y ↦ ((n+1)y − 2∑ εᵢxᵢ)/(n−1)`.
-/

/-- The height after one all-ones reflection move with sign pattern `e`, in dimension `n`. -/
noncomputable def moveHeight (n : ℕ) (x e : Fin n → ℝ) (y : ℝ) : ℝ :=
  ((n + 1) * y - 2 * ∑ i, e i * x i) / (n - 1)




/-!
### Failure of integrality for `n ≥ 4`

The reflection in the all-ones vector subtracts `c = 2·B(v,r)/(n−1)` from each coordinate.
Applied to the first basis vector this is `2/(n−1)`, which is an integer only for `n ≤ 3`.
Consequently the Berggren move exists over `ℤ` precisely in dimensions `n = 2` (triples) and
`n = 3` (quadruples).
-/



end Reflection

end HigherPythagorean


