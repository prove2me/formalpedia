-- Prove2me | solution 1 for softplus_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:58:03.230928+00:00
-- url     : https://prove2.me/submissions/29cf804a-fe8b-4ab9-810a-f898fe13f5e2

-- Sol generated from MachineLearning/ShefferFunction/Lean/SoftplusBasic.lean
import Mathlib
import Definitions.Def_MachineLearning_ShefferFunction_Lean_SoftplusBasic

/-!
# Softplus and the logistic sigmoid: the analytic base of the Sheffer program

`ShefferAlgebra.lean` and `ExtendedTheorems.lean` are written against a module of basic
softplus facts that was not present in this repository, so neither of them compiled.  This
file supplies exactly that base layer:

* `softplus x = log (1 + eˣ)` with its value at `0`, strict monotonicity, continuity,
  differentiability (with the explicit derivative `eˣ/(1+eˣ)`, the logistic sigmoid),
  the reflection identity `σ(x) − σ(−x) = x`, subadditivity and `1`-Lipschitz continuity;
* `logisticSigmoid x = eˣ/(1+eˣ)` with the complement identity `S(x) + S(−x) = 1`.

The reflection identity is what puts the identity function into the Sheffer algebra, and
the Lipschitz bound is the "Lipschitz barrier" that keeps `x²` out of it.
-/

open Real

noncomputable section



theorem one_add_exp_pos (x : ℝ) : 0 < 1 + Real.exp x := by positivity



/-- The derivative of softplus is the logistic sigmoid. -/
theorem softplus_hasDerivAt (x : ℝ) : HasDerivAt softplus (logisticSigmoid x) x :=
  ((Real.hasDerivAt_exp x).const_add 1).log (one_add_exp_pos x).ne'

theorem softplus_differentiable : Differentiable ℝ softplus :=
  fun x => (softplus_hasDerivAt x).differentiableAt

theorem deriv_softplus (x : ℝ) : deriv softplus x = logisticSigmoid x :=
  (softplus_hasDerivAt x).deriv




/-- Softplus is `1`-Lipschitz, because its derivative is the sigmoid, which lies in `(0,1)`. -/
theorem softplus_lipschitz : LipschitzWith 1 softplus := by
  refine lipschitzWith_of_nnnorm_deriv_le softplus_differentiable fun x => ?_
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_one, deriv_softplus, logisticSigmoid, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), div_le_one (one_add_exp_pos x)]
  linarith [Real.exp_pos x]




theorem solution(x y : ℝ) : |softplus x - softplus y| ≤ |x - y| := by
  have h := softplus_lipschitz.dist_le_mul x y
  simpa [Real.dist_eq] using h
