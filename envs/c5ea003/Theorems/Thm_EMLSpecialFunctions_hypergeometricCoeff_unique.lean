-- Prove2me | Theorems.Thm_EMLSpecialFunctions_hypergeometricCoeff_unique
-- name    : EMLSpecialFunctions.hypergeometricCoeff_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:58.165743+00:00
-- url     : https://prove2.me/theorems/c822c08f-ac7f-4159-99a8-921510b33033
-- title:
--   A normalized coefficient sequence satisfying Gauss's recurrence is unique.
-- statement:
--   A normalized coefficient sequence satisfying Gauss's recurrence is unique.
--   Thus the formal solution of Gauss's equation with constant coefficient `1` is
--   precisely the hypergeometric series.
--
--   ```lean
--   theorem EMLSpecialFunctions.hypergeometricCoeff_unique(a b c : ℂ) (u : ℕ → ℂ)
--       (u0 : u 0 = 1)
--       (hu : ∀ n : ℕ, (n + 1) * (c + n) * u (n + 1) =
--         (a + n) * (b + n) * u n)
--       (hc : ∀ n : ℕ, c + n ≠ 0) :
--       u = hypergeometricCoeff a b c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/HypergeometricEquation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/HypergeometricEquation.lean#L66

-- Thm stub generated from Applications/EML/HypergeometricEquation.lean
import Mathlib
import Definitions.Def_Applications_EML_HypergeometricEquation

/-!
# Gauss's hypergeometric differential equation

This file formalizes the coefficient sequence of the Gauss hypergeometric series
`₂F₁(a,b;c;z)` and proves, purely formally, that it is annihilated coefficient by
coefficient by Gauss's differential operator

`z(1-z)y'' + (c-(a+b+1)z)y' - ab y`.

Working with coefficient sequences makes the result independent of analytic
convergence questions and captures the algebraic core of the differential equation.
-/

open EMLSpecialFunctions

theorem EMLSpecialFunctions.hypergeometricCoeff_unique(a b c : ℂ) (u : ℕ → ℂ)
    (u0 : u 0 = 1)
    (hu : ∀ n : ℕ, (n + 1) * (c + n) * u (n + 1) =
      (a + n) * (b + n) * u n)
    (hc : ∀ n : ℕ, c + n ≠ 0) :
    u = hypergeometricCoeff a b c := by sorry
