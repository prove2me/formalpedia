-- Prove2me | Theorems.Thm_HigherPythagorean_lorentz_move_height_bound
-- name    : HigherPythagorean.lorentz_move_height_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:42:13.275985+00:00
-- url     : https://prove2.me/theorems/6ce1542d-0348-4b9c-a0c7-367c334216f5
-- title:
--   Sharp growth constant.
-- statement:
--   **Sharp growth constant.**  One reflection move multiplies the height by at most
--   `(ân+1)/(ânâ1)`.  At `n = 2` this constant is `3+2â2 = (1+â2)Â²` (silver ratio squared,
--   the Berggren case); at `n = 3` it is `2+â3`.
--
--   ```lean
--   theorem HigherPythagorean.lorentz_move_height_bound{n : ℕ} (hn : 2 ≤ n) (x e : Fin n → ℝ) (y : ℝ) (hy : 0 < y)
--       (h : ∑ i, (x i) ^ 2 = y ^ 2) (he : ∀ i, e i = 1 ∨ e i = -1) :
--       moveHeight n x e y ≤ (Real.sqrt n + 1) / (Real.sqrt n - 1) * y := by sorry
--
--   /-!
--   ### Failure of integrality for `n ≥ 4`
--
--   The reflection in the all-ones vector subtracts `c = 2·B(v,r)/(n−1)` from each coordinate.
--   Applied to the first basis vector this is `2/(n−1)`, which is an integer only for `n ≤ 3`.
--   Consequently the Berggren move exists over `ℤ` precisely in dimensions `n = 2` (triples) and
--   `n = 3` (quadruples).
--   -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/LorentzCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/LorentzCore.lean#L154

-- Thm stub generated from Shared/HigherPythagorean/LorentzCore.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_LorentzCore

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

open HigherPythagorean

open Matrix Finset


variable (n : ℕ)




variable {n}






variable {n : ℕ}










/-!
### The all-ones reflection and its growth constant

For the vector `r = (1,…,1;1)` one has `q(r) = n − 1` and the reflection
`s_r(v) = v − (2·B(v,r)/(n−1))·r` subtracts the *same* rational number from every coordinate.
Its effect on the height (last coordinate) is `y ↦ ((n+1)y − 2∑ εᵢxᵢ)/(n−1)`.
-/

theorem HigherPythagorean.lorentz_move_height_bound{n : ℕ} (hn : 2 ≤ n) (x e : Fin n → ℝ) (y : ℝ) (hy : 0 < y)
    (h : ∑ i, (x i) ^ 2 = y ^ 2) (he : ∀ i, e i = 1 ∨ e i = -1) :
    moveHeight n x e y ≤ (Real.sqrt n + 1) / (Real.sqrt n - 1) * y := by sorry
