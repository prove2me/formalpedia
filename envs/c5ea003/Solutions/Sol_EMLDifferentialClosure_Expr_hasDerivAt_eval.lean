-- Prove2me | solution 1 for EMLDifferentialClosure.Expr.hasDerivAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:23:06.29808+00:00
-- url     : https://prove2.me/submissions/49f2633e-35e6-41ad-bd9f-6d173ccbeec9

-- Sol generated from EML/AbstractAlgebra/DifferentialClosure.lean
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
























/-! ## Local inverses and integration -/


/- The original declaration used `Function.LeftInverse g f`, which only says
`g (f x) = x`; the derivative formula at `x` requires `f (g x) = x` instead.
For example, totalized `Real.log` is a left inverse of `Real.exp`, but at negative
arguments its derivative does not satisfy the claimed formula. -/





open EMLDifferentialClosure.Expr in
theorem solution(p : Expr) {x : ℝ} (h : RegularAt p x) :
    HasDerivAt (eval p) (eval (diff p) x) x := by
  induction p with
  | const c => simpa [eval, diff] using hasDerivAt_const (x := x) (c := c)
  | var => simpa [eval, diff] using hasDerivAt_id x
  | add p q ihp ihq =>
      exact (ihp h.1).add (ihq h.2)
  | mul p q ihp ihq =>
      simpa [eval, diff, add_comm] using (ihp h.1).mul (ihq h.2)
  | inv p ih =>
      convert (ih h.1).inv h.2 using 1
      all_goals simp [eval, diff]
      all_goals field_simp
  | exp p ih =>
      simpa [eval, diff, Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (eval p x)).comp x (ih h)
  | log p ih =>
      simpa [eval, diff, Function.comp_def, mul_comm] using
        (Real.hasDerivAt_log h.2).comp x (ih h.1)
