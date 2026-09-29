-- Prove2me | Definitions.Def_Applications_EML_EMLDifferentialEquations
-- name    : Applications_EML_EMLDifferentialEquations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:36.250606+00:00
-- url     : https://prove2.me/theorems/942a9c33-9b21-4224-bb2e-210f686c5c81
-- title:
--   Aether Catalog definitions — Applications_EML_EMLDifferentialEquations
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EML.EMLDifferentialEquations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EML/EMLDifferentialEquations.lean by skeleton subtraction
import Mathlib

/-!
# EML Differential Equations

Exponential–logarithmic (**EML**) functions are the real functions built from the
identity, real constants, `+`, `*`, `⁻¹`, `Real.exp` and `Real.log`.  This file
develops the differential calculus of that class and uses it to analyse the
second-order linear equation

  `y'' = r · y`,   `r` a polynomial,

with the **Airy equation** `y'' = x · y` as the guiding example.

## Contents

* `EMLExpr`, `EMLExpr.eval`, `EMLExpr.D`, `EMLExpr.Regular` — a syntax for EML
  functions, its interpretation, its *symbolic* derivative and the (pointwise)
  regularity predicate saying that all inversions and logarithms occurring in an
  expression have nonzero argument at a point.
* `EMLExpr.hasDerivAt_eval` — **correctness of symbolic differentiation**: at a
  regular point the analytic derivative of `eval e` is `eval (D e)`.  In
  particular the class of EML functions is closed under differentiation
  (`EMLExpr.Regular.D`).
* `EMLExpr.exp_solves_firstOrder` and `EMLExpr.firstOrder_unique` — the complete
  solution theory of the first-order linear EML equation `y' = c · y`: the
  exponential of an antiderivative solves it, and every solution is a constant
  multiple of that one.
* `riccati_no_rational_solution` — the **algebraic Kovacic obstruction**: if
  `r` is a polynomial of odd degree then the Riccati equation `u' + u² = r` has
  no solution `u = P/Q` in the field of rational functions.
* `airy_no_rational_logDeriv` — the analytic form: no nowhere-vanishing solution
  of `y'' = x·y` has a rational logarithmic derivative.
* `airy_no_eml_exponential_solution` — consequently the Airy equation has no
  solution of the EML shape `y = exp ∘ F` with `F'` rational; this is exactly
  the failure of the first Kovacic case for Airy's equation.
* `riccati_odd_degree_sharp`, `exp_half_sq_solves` — sharpness: for the
  even-degree coefficient `r = x² + 1` the Riccati equation *does* have the
  rational solution `u = x`, and `y = exp (x²/2)` is a genuine EML solution of
  `y'' = (x²+1) y`.
-/

namespace EMLDiffEq

open Polynomial

/-! ## 1. Syntax and calculus of EML functions -/

/-- Syntax for exponential–logarithmic expressions in one real variable. -/
inductive EMLExpr : Type
  | X : EMLExpr
  | const : ℝ → EMLExpr
  | add : EMLExpr → EMLExpr → EMLExpr
  | mul : EMLExpr → EMLExpr → EMLExpr
  | inv : EMLExpr → EMLExpr
  | exp : EMLExpr → EMLExpr
  | log : EMLExpr → EMLExpr

namespace EMLExpr

/-- Interpretation of an EML expression as a real function (junk values `0⁻¹ = 0`
and `Real.log 0 = 0` are used outside the regular locus). -/
noncomputable def eval : EMLExpr → ℝ → ℝ
  | X, x => x
  | const c, _ => c
  | add a b, x => eval a x + eval b x
  | mul a b, x => eval a x * eval b x
  | inv a, x => (eval a x)⁻¹
  | exp a, x => Real.exp (eval a x)
  | log a, x => Real.log (eval a x)

/-- Symbolic derivative of an EML expression.  The point of the construction is
that the class of EML expressions is *closed* under it. -/
def D : EMLExpr → EMLExpr
  | X => const 1
  | const _ => const 0
  | add a b => add (D a) (D b)
  | mul a b => add (mul (D a) b) (mul a (D b))
  | inv a => mul (const (-1)) (mul (D a) (mul (inv a) (inv a)))
  | exp a => mul (D a) (exp a)
  | log a => mul (D a) (inv a)

/-- `Regular e x` says that every inversion and every logarithm occurring in `e`
has nonzero argument at `x`; this is the precise domain condition under which
symbolic differentiation is analytically valid. -/
def Regular : EMLExpr → ℝ → Prop
  | X, _ => True
  | const _, _ => True
  | add a b, x => Regular a x ∧ Regular b x
  | mul a b, x => Regular a x ∧ Regular b x
  | inv a, x => Regular a x ∧ eval a x ≠ 0
  | exp a, x => Regular a x
  | log a, x => Regular a x ∧ eval a x ≠ 0




/-! ## 2. First-order linear EML equations -/



end EMLExpr

/-! ## 3. The algebraic Kovacic obstruction -/

section Algebraic

variable {K : Type*} [Field K]










end Algebraic

/-! ## 4. From analysis to algebra: Airy has no EML exponential solution -/



/-! ## 5. Sharpness of the odd-degree hypothesis -/




end EMLDiffEq


