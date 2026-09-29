-- Prove2me | Definitions.Def_LinearOptimization_ReducedCost
-- name    : LinearOptimization_ReducedCost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T17:22:16.509826+00:00
-- url     : https://prove2.me/theorems/6eb50a0b-cdca-4c58-b739-3709a4b2086e
-- title:
--   Reduced cost $\bar{c}_j = c_j - c_B'B^{-1}A_j$
-- statement:
--   **(Definition 3.2)** Let $x$ be a basic solution, let $B$ be an associated basis matrix, and let $c_B$ be the vector of costs of the basic variables. For each $j$, we define the *reduced cost* $\bar{c}_j$ of the variable $x_j$ according to the formula
--
--   $$\bar{c}_j = c_j - c_B'B^{-1}A_j.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 3.2, p. 84

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_BasicSolution

/-!
Reduced costs.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 3.2 (p. 84)**: "Let `x` be a basic
solution, let `B` be an associated basis matrix, and let `c_B` be the
vector of costs of the basic variables. For each `j`, we define the
*reduced cost* `c̄_j` of the variable `x_j` according to the formula
`c̄_j = c_j − c_B'B⁻¹A_j`."

`B⁻¹` is Lean's `Matrix.inv` (junk value `0` when `basisMatrix A B` is not
invertible); every theorem consuming `reducedCost` carries the
`IsStdBasis A B` guard, which makes the basis matrix invertible.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 3.2 (p. 84).** The reduced cost of the variable `x_j`
with respect to the basis `B`: `c̄_j = c_j − c_B'B⁻¹A_j`, where `c_B` is
the vector of costs of the basic variables and `A_j` is the `j`th column
of `A`. -/
noncomputable def reducedCost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (B : Fin m ↪ Fin n) (j : Fin n) : ℝ :=
  c j - (fun i => c (B i)) ⬝ᵥ (basisMatrix A B)⁻¹.mulVec (fun i' => A i' j)

/-- Book remark, p. 86: "the reduced cost of every basic variable is zero"
(stated under the invertibility of the basis matrix, which `IsStdBasis A B`
supplies). -/
theorem reducedCost_basic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (B : Fin m ↪ Fin n) [Invertible (basisMatrix A B)]
    (i : Fin m) : reducedCost A c B (B i) = 0 := by
  have hcol : (basisMatrix A B)⁻¹.mulVec (fun i' => A i' (B i)) = Pi.single i 1 := by
    funext k
    have h1 : (basisMatrix A B)⁻¹.mulVec (fun i' => A i' (B i)) k
        = ((basisMatrix A B)⁻¹ * basisMatrix A B) k i := by
      simp [Matrix.mulVec, Matrix.mul_apply, dotProduct, basisMatrix]
    rw [h1, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply, Pi.single_apply]
  unfold reducedCost
  rw [hcol, dotProduct_single]
  simp

end LinearOptimization


