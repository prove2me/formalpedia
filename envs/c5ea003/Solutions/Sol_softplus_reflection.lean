-- Prove2me | solution 1 for softplus_reflection
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:03:53.173987+00:00
-- url     : https://prove2.me/submissions/9898630b-8d4d-4f22-a441-85afe2e99354

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













theorem solution(x : ℝ) : softplus x - softplus (-x) = x := by
  have h : 1 + Real.exp x = Real.exp x * (1 + Real.exp (-x)) := by
    rw [mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  rw [softplus, softplus, h, Real.log_mul (Real.exp_ne_zero x) (one_add_exp_pos (-x)).ne',
    Real.log_exp]
  ring
