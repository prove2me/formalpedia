-- Prove2me | Definitions.Def_Couret_RecohRationalRoots_2e1442988636
-- name    : Couret_RecohRationalRoots_2e1442988636
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:31.911877+00:00
-- url     : https://prove2.me/theorems/17087fcc-ca6b-47d3-a118-7eb8d9bd97d3
-- title:
--   Rational Machin and phase approximation constructions
-- statement:
--   For rational $x$ and natural $n$, define $$A_n(x)=\sum_{k<n}\frac{(-1)^kx^{2k+1}}{2k+1},\qquad E_n(x)=\frac{x(x^2)^n}{1-x^2}.$$ Set $\pi_n=16A_n(1/5)-4A_n(1/239)$ and $e_n=16E_n(1/5)+4E_n(1/239)$. Rational coordinate multiplication, scaling, powers and their additive interpretation $V(a,b)=a+bi$ define the rational Taylor pair $T_n(t)=\sum_{k<n}(it)^k/k!$. The phase center for turn $t$ and precision parameters $m,n$ is $T_n(2\pi_m t)$; its specified error expression is $2e_m+2\,8^n/n!$. All finite calculations use rational arithmetic. The raw functions are defined on all their rational and natural inputs; valid analytic error estimates require the separate interval, precision and center-size hypotheses and are not asserted for arbitrary inputs by this bundle.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohRationalRoots.lean; source file SHA-256 dc918d91d9f34ce1258fdf43b9d5f7cfbb17e66a2ab684f7e07f0e5f725df81c

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false

/-!
Rational centres for complex phases, with explicit analytic error bounds.
The centres use Machin's formula and a finite exponential Taylor polynomial.
All finite arithmetic is rational.  The bounds depend on two natural-number
precision parameters, and therefore can be checked without a real comparison.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

def recohArctanPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (-1 : ℚ) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

def recohArctanError (x : ℚ) (n : ℕ) : ℚ :=
  x * (x ^ 2) ^ n / (1 - x ^ 2)



def recohPiPartial (n : ℕ) : ℚ :=
  16 * recohArctanPartial (1 / 5) n - 4 * recohArctanPartial (1 / 239) n

def recohPiError (n : ℕ) : ℚ :=
  16 * recohArctanError (1 / 5) n + 4 * recohArctanError (1 / 239) n



def recohRationalComplexMul (z w : RecohRationalComplex) : RecohRationalComplex :=
  (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

def recohRationalComplexScale (a : ℚ) (z : RecohRationalComplex) : RecohRationalComplex :=
  (a * z.1, a * z.2)

def recohRationalComplexPow (z : RecohRationalComplex) : ℕ → RecohRationalComplex
  | 0 => (1, 0)
  | n + 1 => recohRationalComplexMul (recohRationalComplexPow z n) z

noncomputable def recohRationalComplexAddHom : RecohRationalComplex →+ ℂ where
  toFun := recohRationalComplexValue
  map_zero' := by apply Complex.ext <;> simp [recohRationalComplexValue]
  map_add' z w := by apply Complex.ext <;> simp [recohRationalComplexValue]







def recohRationalExpTaylor (t : ℚ) (n : ℕ) : RecohRationalComplex :=
  ∑ k ∈ Finset.range n,
    recohRationalComplexScale (1 / (k.factorial : ℚ)) (recohRationalComplexPow (0, t) k)



def recohTaylorError (n : ℕ) : ℚ := 2 * (8 : ℚ) ^ n / n.factorial





def recohRationalPhase (turn : ℚ) (machinTerms taylorTerms : ℕ) : RecohRationalComplex :=
  recohRationalExpTaylor (2 * recohPiPartial machinTerms * turn) taylorTerms

def recohRationalPhaseError (machinTerms taylorTerms : ℕ) : ℚ :=
  2 * recohPiError machinTerms + recohTaylorError taylorTerms



end Couret.STROBO2TORS


