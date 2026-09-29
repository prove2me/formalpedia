-- Prove2me | Theorems.Thm_shefferExpr_lipschitz
-- name    : shefferExpr_lipschitz
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:02:43.726954+00:00
-- url     : https://prove2.me/theorems/8ec9b702-1605-462a-b7f5-7264fd747c69
-- title:
--   Every Sheffer expression is globally Lipschitz.
-- statement:
--   **Every Sheffer expression is globally Lipschitz.**  The constant is produced by
--   structural induction: `1` for softplus, `C·|a|` for an affine pre-composition,
--   `|α|C₁ + |β|C₂` for an affine combination and `C₁C₂` for a composition.
--
--   ```lean
--   theorem shefferExpr_lipschitz(e : ShefferExpr) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |e.eval x - e.eval y| ≤ C * |x - y| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/ShefferFunction/Lean/ShefferFoundations.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/ShefferFunction/Lean/ShefferFoundations.lean#L30

-- Thm stub generated from MachineLearning/ShefferFunction/Lean/ShefferFoundations.lean
import Mathlib
import Definitions.Def_MachineLearning_ShefferFunction_Lean_ShefferAlgebra

/-!
# The Lipschitz barrier for the Sheffer algebra

`ExtendedTheorems.lean` is written against three upstream modules that are absent from this
repository (`ShefferAI.Lean.UniversalApproximation`, `.FutureTheorems`, `.AdvancedTheorems`,
`.NewTheorems`).  The results it actually uses from them are the closure of the Sheffer
algebra under scalar multiplication and the exclusion of `x²`.  This file supplies both,
from scratch.

The exclusion of `x²` is the **Lipschitz barrier**: every Sheffer expression is globally
Lipschitz, because the only nonlinear building block, softplus, is `1`-Lipschitz and the
three closure operations (affine pre-composition, affine combination, composition) all
preserve global Lipschitz continuity.  Since `x ↦ x²` is not globally Lipschitz on `ℝ`, it
is not in the algebra — and hence the algebra is not closed under pointwise multiplication.
-/

open Real

noncomputable section

theorem shefferExpr_lipschitz(e : ShefferExpr) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |e.eval x - e.eval y| ≤ C * |x - y| := by sorry
