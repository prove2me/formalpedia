-- Prove2me | Definitions.Def_EML_AbstractAlgebra_DifferentialClosure
-- name    : EML_AbstractAlgebra_DifferentialClosure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:15.54426+00:00
-- url     : https://prove2.me/theorems/0aa4d2ea-c860-4a08-a3eb-5cc00aeffd3f
-- title:
--   Aether Catalog definitions — EML_AbstractAlgebra_DifferentialClosure
-- statement:
--   Definition bundle for the Aether Catalog module `EML.AbstractAlgebra.DifferentialClosure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/AbstractAlgebra/DifferentialClosure.lean by skeleton subtraction
import Mathlib

/-!
# Differential closure of rational exponential--logarithmic expressions

We use a precise expression language with real constants, the identity, field operations,
`exp`, and `log`.  Its symbolic derivative is again an expression.  This gives a rigorous
closure theorem for the regular (everywhere differentiable) members of the represented
function class.  Composition is implemented by syntactic substitution.
-/

namespace EMLDifferentialClosure

/-- Rational exponential--logarithmic expressions in one real variable. -/
inductive Expr where
  | const : ℝ → Expr
  | var : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | inv : Expr → Expr
  | exp : Expr → Expr
  | log : Expr → Expr

namespace Expr

/-- Real evaluation, using Lean's totalized inverse and logarithm. -/
noncomputable def eval : Expr → ℝ → ℝ
  | const c, _ => c
  | var, x => x
  | add p q, x => eval p x + eval q x
  | mul p q, x => eval p x * eval q x
  | inv p, x => (eval p x)⁻¹
  | exp p, x => Real.exp (eval p x)
  | log p, x => Real.log (eval p x)

/-- Substitute `q` for the variable in `p`. -/
def subst : Expr → Expr → Expr
  | const c, _ => const c
  | var, q => q
  | add p r, q => add (subst p q) (subst r q)
  | mul p r, q => mul (subst p q) (subst r q)
  | inv p, q => inv (subst p q)
  | exp p, q => exp (subst p q)
  | log p, q => log (subst p q)

/-- Formal derivative. -/
def diff : Expr → Expr
  | const _ => const 0
  | var => const 1
  | add p q => add (diff p) (diff q)
  | mul p q => add (mul (diff p) q) (mul p (diff q))
  | inv p => mul (const (-1)) (mul (diff p) (inv (mul p p)))
  | exp p => mul (diff p) (exp p)
  | log p => mul (diff p) (inv p)

/-- Domain condition under which all ordinary chain-rule steps in an expression are valid. -/
def RegularAt : Expr → ℝ → Prop
  | const _, _ => True
  | var, _ => True
  | add p q, x => RegularAt p x ∧ RegularAt q x
  | mul p q, x => RegularAt p x ∧ RegularAt q x
  | inv p, x => RegularAt p x ∧ eval p x ≠ 0
  | exp p, x => RegularAt p x
  | log p, x => RegularAt p x ∧ eval p x ≠ 0




end Expr

/-- A real function is EML when represented by a rational exponential--logarithmic expression. -/
def IsEML (f : ℝ → ℝ) : Prop := ∃ p : Expr, Expr.eval p = f















/-! ## Local inverses and integration -/


/- The original declaration used `Function.LeftInverse g f`, which only says
`g (f x) = x`; the derivative formula at `x` requires `f (g x) = x` instead.
For example, totalized `Real.log` is a left inverse of `Real.exp`, but at negative
arguments its derivative does not satisfy the claimed formula. -/




end EMLDifferentialClosure


