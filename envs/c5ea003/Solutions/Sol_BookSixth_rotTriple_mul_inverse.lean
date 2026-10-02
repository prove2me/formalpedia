-- Prove2me | solution 1 for BookSixth.rotTriple_mul_inverse
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-26T15:17:05.497827+00:00
-- url     : https://prove2.me/submissions/5fbfbdfa-0a1a-404f-af2a-fa61b4d42d3b

import Mathlib
import Definitions.Def_BookSixthRotations3
open Matrix
noncomputable section

/-- **Disproof of `BookSixth.rotTriple_mul_inverse`.**

The target asserts

```
rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
  (rot12Matrix (-θ3) * rot02Matrix (-θ2) * rot01Matrix (-θ1)) = 1
```

for all `θ1 θ2 θ3`. This is false. The three matrices rotate about *different* axes, so
the product `R := rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1` is a genuine rotation,
but inverting a product requires **reversing the order** of the factors:

```
R⁻¹ = rot01Matrix (-θ1) * rot02Matrix (-θ2) * rot12Matrix (-θ3)
```

The target instead keeps the original order, and the natural-language statement states the
error explicitly — "multiplying it by the same product taken at the OPPOSITE angles" — since
`R02Matrix (-θ2) * R01Matrix (-θ1)` is *not* `(R02Matrix θ2 * R01Matrix θ1)⁻¹` when the
two rotations are about different axes.

**The counterexample.** Take `θ1 = θ2 = π/4` and `θ3 = 0`. Then `rot12Matrix 0 = 1`, so
the product is `R = rot02Matrix (π/4) * rot01Matrix (π/4)`, and writing
`c = s = Real.cos (π/4) = 1/√2` (so `c * s = 1/2`) the first row of `R` is
`[c², -c * s, -s²] = [1/2, -1/2, -1/√2]`, while the second column of the negated product
`S = rot02Matrix (-π/4) * rot01Matrix (-π/4)` is `[1/2, 1/√2, -1/2]`. Hence

```
(R * S) 0 1 = (1/2)(1/2) + (-1/2)(1/√2) + (-1/√2)(-1/2) = 1/4,
```

whereas `(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0` because `0 ≠ 1`. So the `(0,1)`-entry of
the claimed identity is `1/4` instead of `0`.

The same computation shows the identity *is* true when at most one angle is nonzero, which
is why the error is not visible in a one-axis test: for `θ2 = θ3 = 0` the two orders
coincide. The failure needs two or more nonzero angles, and `π/4, π/4, 0` is the smallest
such choice.

**The corrected statement** is
`rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
  (rot01Matrix (-θ1) * rot02Matrix (-θ2) * rot12Matrix (-θ3)) = 1`,
which is the genuine group law. `R * Rᵀ = 1` also holds. The sibling
`BookSixth.rotTriple_mul_eq_one` (`2775a585-e553-4a50-8ddb-817ccbd2c4cf`), which claims
`R * R = 1`, is false for the same reason: `R` is a rotation by a nonzero angle, not an
involution.

mathematical unit: a counterexample to the product-inverse identity, namely
`θ1 = θ2 = π/4`, `θ3 = 0`, at which the `(0,1)`-entry is `1/4` rather than `0`.

first remote check: the evaluation of the `(0,1)`-entry of `R * S`, which is
`Real.cos (π/4) ^ 2 * … + …` and must come out as `1/4`.

helper / child boundary: none; the disproof is the single entry computation.

split decision: keep it whole.

first remote unit: `ext 0 1` and the `Real.cos (π/4) = 1/√2` evaluation. -/
theorem solution : ¬(∀ θ1 θ2 θ3 : ℝ,
    rot12Matrix θ3 * rot02Matrix θ2 * rot01Matrix θ1 *
      (rot12Matrix (-θ3) * rot02Matrix (-θ2) * rot01Matrix (-θ1)) = 1) := by
  intro h
  -- Instantiate at `θ1 = θ2 = π/4`, `θ3 = 0`, and read off the `(0,1)`-entry.
  have h0 := h (Real.pi / 4) (Real.pi / 4) 0
  -- `(1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0` because `0 ≠ 1` (Matrix.one_apply,
  -- `Data/Matrix/Diagonal.lean:234`).
  have hzero : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 1 = 0 := by simp [Matrix.one_apply]
  have h01 : (rot12Matrix 0 * rot02Matrix (Real.pi / 4) * rot01Matrix (Real.pi / 4) *
      (rot12Matrix 0 * rot02Matrix (-(Real.pi / 4)) *
        rot01Matrix (-(Real.pi / 4)))) 0 1 = 0 := by
    have := congr_fun (congr_fun h0 (0 : Fin 3)) (1 : Fin 3)
    rw [hzero] at this
    rw [neg_zero] at this
    exact this
  -- The left-hand side is `1/4`, not `0`.  `rot12Matrix 0` is the identity, so it is
  -- rewritten away by `Matrix.one_mul`; `Real.cos_pi_div_four` and `Real.sin_pi_div_four`
  -- (`Analysis/SpecialFunctions/Trigonometric/Basic.lean:714` and `:721`) turn every
  -- remaining `cos`/`sin` of `π/4` into `√2 / 2`.
  --
  -- One `norm_num` over the whole set.  `rot12Matrix 0` is the identity, so `rot12Matrix`
  -- can be unfolded unconditionally; `Matrix.mul_apply` exposes the contraction sum and
  -- `Fin.sum_univ_succ` expands it over `Fin 3`; `![a, b, c] i j` is
  -- `vecCons a (vecCons b (vecCons c vecEmpty)) i j` and `vecCons h t = Fin.cons h t`
  -- (`Data/Fin/VecNotation.lean:59`), so `Fin.cons_zero` / `Fin.cons_succ` evaluate it on
  -- the concrete index; and `Real.cos_neg` / `Real.sin_neg` turn `-(π/4)` into `π/4` for
  -- the `[simp]` evaluation lemmas.
  norm_num [rot12Matrix, rot02Matrix, rot01Matrix, Matrix.mul_apply, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Real.cos_neg, Real.sin_neg] at h01
  -- The residual is `(√2/2)³ = 0`, and `(√2/2)³ = √2 / 4`.  `norm_num` normalises ring
  -- structure but cannot decide irrationality, so the last step needs the two facts about
  -- `√2`: `Real.sq_sqrt` (`Data/Real/Sqrt.lean:178`) and `Real.sqrt_pos`.  `nlinarith` is a
  -- decision procedure over the reals and does refute `√2 / 2 ^ 3 = 0` from them.
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  nlinarith [hsq, hpos]
