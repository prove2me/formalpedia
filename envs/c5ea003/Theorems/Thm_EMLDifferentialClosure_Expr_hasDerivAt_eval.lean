-- Prove2me | Theorems.Thm_EMLDifferentialClosure_Expr_hasDerivAt_eval
-- name    : EMLDifferentialClosure.Expr.hasDerivAt_eval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:22:30.446645+00:00
-- url     : https://prove2.me/theorems/f1646816-43a2-4aad-8f1d-e8d727e295b4
-- title:
--   The symbolic derivative is correct at every regular point.
-- statement:
--   The symbolic derivative is correct at every regular point.
--
--   ```lean
--   theorem EMLDifferentialClosure.Expr.hasDerivAt_eval(p : Expr) {x : ℝ} (h : RegularAt p x) :
--       HasDerivAt (eval p) (eval (diff p) x) x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `EML/AbstractAlgebra/DifferentialClosure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/EML/AbstractAlgebra/DifferentialClosure.lean#L70

-- Thm stub generated from EML/AbstractAlgebra/DifferentialClosure.lean
import Mathlib
import Definitions.Def_EML_AbstractAlgebra_DifferentialClosure

/-!
# Differential closure of rational exponential--logarithmic expressions

We use a precise expression language with real constants, the identity, field operations,
`exp`, and `log`.  Its symbolic derivative is again an expression.  This gives a rigorous
closure theorem for the regular (everywhere differentiable) members of the represented
function class.  Composition is implemented by syntactic substitution.
-/

open EMLDifferentialClosure


open Expr

theorem EMLDifferentialClosure.Expr.hasDerivAt_eval(p : Expr) {x : ℝ} (h : RegularAt p x) :
    HasDerivAt (eval p) (eval (diff p) x) x := by sorry
