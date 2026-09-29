-- Prove2me | Definitions.Def_MachineLearning_DerivDepth_IterExp
-- name    : MachineLearning_DerivDepth_IterExp
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:40.220458+00:00
-- url     : https://prove2.me/theorems/68306201-c7fa-49e1-a046-2ffa2a5ee817
-- title:
--   Aether Catalog definitions — MachineLearning_DerivDepth_IterExp
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.DerivDepth.IterExp`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/DerivDepth/IterExp.lean by skeleton subtraction
import Mathlib

/-!
# Iterated Exponentials: Derivative Theory

This file develops the derivative theory of iterated exponentials, establishing that
derivative growth is a semantic shadow of compositional depth.

## Main Definitions

- `iterExp k x`: the k-fold iterated exponential, `exp^[k](x)`
- `depthMajorant d M`: the tower bound `iterExp d M`
- `iterExpDerivProd k x`: the closed-form derivative `∏ i < k, iterExp (i+1) x`

## Main Results

- `iterExp_hasDerivAt`: closed-form derivative formula for iterExp
- `iterExp_deriv_lower_bound_at_one`: derivative of `iterExp (k+1)` at 1 is ≥ `iterExp (k+1) 1`
- `exp_sq_le`: key inequality `t² ≤ exp(t)` for `t ≥ 0`
- `iterExp_ge_self`: `iterExp k M ≥ M` for `M ≥ 0`

These results form the analytic foundation for depth separation via derivative obstruction.
-/

noncomputable section
open Real Finset

/-! ## Core Definitions -/

/-- The iterated exponential: `iterExp 0 x = x`, `iterExp (k+1) x = exp(iterExp k x)`. -/
def iterExp : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.exp (iterExp n x)

/-- The depth majorant: the tower bound for derivative growth at depth `d` with
    subexpression bound `M`. This is simply `iterExp d M`. -/
def depthMajorant (d : ℕ) (M : ℝ) : ℝ := iterExp d M

/-- The closed-form derivative of `iterExp k` at point `x`:
    the product `∏ i ∈ range k, iterExp (i+1) x`. -/
def iterExpDerivProd (k : ℕ) (x : ℝ) : ℝ :=
  ∏ i ∈ Finset.range k, iterExp (i + 1) x

/-! ## Basic Properties of iterExp -/







/-
Monotonicity: `depthMajorant` is monotone in the depth parameter.
-/

/-! ## Key Inequality: exp(t) ≥ t² for t ≥ 0 -/

/-
The fundamental inequality: `exp(t) ≥ t²` for `t ≥ 0`.
    This is the engine that converts multiplicative derivative accumulation
    into tower-bounded growth.
-/

/-
Consequence: `a * b ≤ exp(b)` when `0 ≤ a ≤ b`.
-/

/-! ## Differentiability -/


/-! ## Derivative Formula -/




/-! ## Derivative Positivity -/

/-
The derivative product is positive for `x > 0`.
-/

/-
The derivative of `iterExp k` is nonneg on `[0,1]`.
-/

/-! ## Lower Bound at x = 1 -/


/-
**Key lower bound**: The derivative of `iterExp (k+1)` at `x = 1`
    is at least `iterExp (k+1) 1`.

    This witnesses the near-sharpness of the depth majorant bound:
    the derivative is at least as large as the top tower level.

    Proof: the derivative product at 1 contains `iterExp (k+1) 1` as a factor,
    and all other factors are ≥ 1.
-/

/-
The depth majorant at depth `k` and base `1` is a lower bound
    for the derivative of the next tower level at `x = 1`.
-/

end


