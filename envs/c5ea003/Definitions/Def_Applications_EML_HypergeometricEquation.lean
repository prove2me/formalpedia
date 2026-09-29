-- Prove2me | Definitions.Def_Applications_EML_HypergeometricEquation
-- name    : Applications_EML_HypergeometricEquation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:41.024584+00:00
-- url     : https://prove2.me/theorems/22968b39-e636-4b61-9c2e-6e4011b1e868
-- title:
--   Aether Catalog definitions — Applications_EML_HypergeometricEquation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EML.HypergeometricEquation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EML/HypergeometricEquation.lean by skeleton subtraction
import Mathlib

/-!
# Gauss's hypergeometric differential equation

This file formalizes the coefficient sequence of the Gauss hypergeometric series
`₂F₁(a,b;c;z)` and proves, purely formally, that it is annihilated coefficient by
coefficient by Gauss's differential operator

`z(1-z)y'' + (c-(a+b+1)z)y' - ab y`.

Working with coefficient sequences makes the result independent of analytic
convergence questions and captures the algebraic core of the differential equation.
-/

namespace EMLSpecialFunctions

/-- Coefficients of the formal Gauss hypergeometric series.  The recurrence is
`u₀ = 1` and
`uₙ₊₁ = ((a+n)(b+n))/((c+n)(n+1)) uₙ`.
When `c` is not a nonpositive integer, these are the usual coefficients
`(a)ₙ(b)ₙ / ((c)ₙ n!)`. -/
noncomputable def hypergeometricCoeff (a b c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => ((a + n) * (b + n) / ((c + n) * (n + 1))) *
      hypergeometricCoeff a b c n

/-- The coefficient of `zⁿ` in Gauss's differential operator applied to a
formal series with coefficient sequence `u`. -/
def gaussOperatorCoeff (a b c : ℂ) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n + 1) * (c + n) * u (n + 1) - (a + n) * (b + n) * u n






end EMLSpecialFunctions


