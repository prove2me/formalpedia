-- Prove2me | Definitions.Def_MachineLearning_ShefferFunction_Lean_SoftplusBasic
-- name    : MachineLearning_ShefferFunction_Lean_SoftplusBasic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:59:06.98475+00:00
-- url     : https://prove2.me/theorems/26abea4e-20ed-45d3-b967-033eb206a3fa
-- title:
--   Aether Catalog definitions — MachineLearning_ShefferFunction_Lean_SoftplusBasic
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.ShefferFunction.Lean.SoftplusBasic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/ShefferFunction/Lean/SoftplusBasic.lean by skeleton subtraction
import Mathlib

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

/-- The softplus activation `σ(x) = log(1 + eˣ)`. -/
def softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- The logistic sigmoid `S(x) = eˣ/(1 + eˣ)`, the derivative of softplus. -/
def logisticSigmoid (x : ℝ) : ℝ := Real.exp x / (1 + Real.exp x)













end


