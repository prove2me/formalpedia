-- Prove2me | Theorems.Thm_softplus_abs_sub_le
-- name    : softplus_abs_sub_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:48.002131+00:00
-- url     : https://prove2.me/theorems/006c459f-805e-4097-b316-01f5891b5f3f
-- title:
--   Softplus abs sub le
-- statement:
--   Formal statement of `softplus_abs_sub_le` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem softplus_abs_sub_le(x y : ℝ) : |softplus x - softplus y| ≤ |x - y| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/ShefferFunction/Lean/SoftplusBasic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/ShefferFunction/Lean/SoftplusBasic.lean#L74

-- Thm stub generated from MachineLearning/ShefferFunction/Lean/SoftplusBasic.lean
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

theorem softplus_abs_sub_le(x y : ℝ) : |softplus x - softplus y| ≤ |x - y| := by sorry
