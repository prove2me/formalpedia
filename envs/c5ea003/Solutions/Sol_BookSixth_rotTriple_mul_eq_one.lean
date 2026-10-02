-- Prove2me | solution 1 for BookSixth.rotTriple_mul_eq_one
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-26T15:21:43.878715+00:00
-- url     : https://prove2.me/submissions/8c991bb2-51ec-4d8d-b240-b8e83619c141

import Mathlib
import Definitions.Def_BookSixthRotations3
open Matrix
noncomputable section

/-- **Disproof of `BookSixth.rotTriple_mul_eq_one`.**

The target asserts that the three-fold rotation

```
R := rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1
```

is its own inverse, i.e. `R * R = 1`. This is false. Each `rot` matrix is an individual
rotation, and `rot01Matrix θ * rot01Matrix θ = rot01Matrix (2 * θ)`, so the product of the
three is a rotation by the *sum* of the three angles, not by `0`. It is an involution only
when that sum is a multiple of `π`.

The natural-language statement of the target asserts the error explicitly: "each rotation
matrix is itself an involution, because the product of a planar rotation by `θ` with the
same rotation by `-θ` is the identity". That is true of a *single* rotation matrix, and the
sibling `BookSixth.rotTriple_mul_inverse` (`7d284dcc-d651-41f2-a942-6bd495e15fa0`, now
**Disproved** as candidate 3469) is the correct version of that idea. Two errors are being
made at once here: the individual matrices are not involutions, and the product of matrices
about *different* axes does not reverse by negating the angles in the same order.

**The counterexample.** Take `θ1 = π/4`, `θ2 = θ3 = 0`. Then `rot12Matrix 0 = 1` and
`rot02Matrix 0 = 1`, so `R = rot01Matrix (π/4)` and `R * R = rot01Matrix (π/2)`. Its
`(0,1)`-entry is `-(Real.sin (π/2)) = -1`, whereas `(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0`
because `0 ≠ 1`.

Only the `(0,1)`-entry is needed, and it is read off `rot01Matrix θ` directly: its
`(0,1)`-entry is `-Real.sin θ`. So `R * R` at `(0,1)` is the contribution
`(rot01Matrix (π/4) * rot01Matrix (π/4)) 0 1 = -sin(π/4) * cos(π/4) + cos(π/4) *
(-sin(π/4)) = -2 * (√2/2) * (√2/2) = -1`.

mathematical unit: a counterexample to `R * R = 1`, namely `θ1 = π/4`, `θ2 = θ3 = 0`, at
which the `(0,1)`-entry of `R * R` is `-1` rather than `0`.

first remote check: the `(0,1)`-entry of the product, which is
`-√2 / 2 * (√2 / 2) + √2 / 2 * -(√2 / 2) = -1`.

helper / child boundary: none; the disproof is the single entry computation.

split decision: keep it whole.

first remote unit: `Matrix.mul_apply` and `Fin.sum_univ_succ` on the `(0,1)`-entry, then
`Real.cos_pi_div_four` and `Real.sin_pi_div_four`. -/
theorem solution : ¬(∀ θ1 θ2 θ3 : ℝ,
    rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
      rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 = 1) := by
  intro h
  have h0 := h (Real.pi / 4) 0 0
  -- `(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0` because `0 ≠ 1` (`Matrix.one_apply`,
  -- `Data/Matrix/Diagonal.lean:234`).
  have hzero : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0 := by simp [Matrix.one_apply]
  have h01 : (rot12Matrix 0 * rot02Matrix 0 * rot01Matrix (Real.pi / 4) *
      rot12Matrix 0 * rot02Matrix 0 * rot01Matrix (Real.pi / 4)) 0 1 = 0 := by
    have hx := congr_fun (congr_fun h0 (0 : Fin 3)) (1 : Fin 3)
    rw [hzero] at hx
    simpa using hx
  -- The left-hand side is `-1`, not `0`.  `rot12Matrix 0` and `rot02Matrix 0` are the
  -- identity, `![a, b, c] 0 1` is the middle entry `b` (`Fin.cons_zero` then
  -- `Fin.cons_succ`), `Matrix.mul_apply` plus `Fin.sum_univ_succ` expands the contraction,
  -- and `Real.cos_pi_div_four` / `Real.sin_pi_div_four`
  -- (`Analysis/SpecialFunctions/Trigonometric/Basic.lean:714` and `:721`) evaluate the
  -- angle.
  norm_num [rot12Matrix, rot02Matrix, rot01Matrix, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ] at h01
