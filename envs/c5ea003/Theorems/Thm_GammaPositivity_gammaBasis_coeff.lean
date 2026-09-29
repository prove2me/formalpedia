-- Prove2me | Theorems.Thm_GammaPositivity_gammaBasis_coeff
-- name    : GammaPositivity.gammaBasis_coeff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:05.08873+00:00
-- url     : https://prove2.me/theorems/d960843e-47f1-4476-ac97-4f4091a2e8a1
-- title:
--   Closed form for the coefficients of a γ-basis element.
-- statement:
--   Closed form for the coefficients of a γ-basis element.
--
--   ```lean
--   theorem GammaPositivity.gammaBasis_coeff(n i k : ℕ) :
--       (gammaBasis n i).coeff k =
--         if i ≤ k then ((n - 2 * i).choose (k - i) : ℝ) else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GammaPositivity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GammaPositivity.lean#L55

-- Thm stub generated from Probability/GammaPositivity.lean
import Mathlib
import Definitions.Def_Probability_GammaPositivity

/-!
# γ-positivity of symmetric (palindromic) polynomials

This file develops the elementary theory of **γ-positivity** for real polynomials,
the exact algebraic property appearing in the study of Ehrhart `h*`-polynomials of
symmetric edge polytopes.

For a degree parameter `n`, the *γ-basis* of the space of polynomials that are
symmetric about `n/2` is
`{ t^i (1+t)^(n-2i) : 0 ≤ i ≤ ⌊n/2⌋ }`.
A polynomial `p` is **γ-positive of order `n`** if it is a nonnegative real
combination of these basis elements.

The main results here:

* `gammaBasis_coeff` — closed form for the coefficients of a basis element in terms
  of binomial coefficients;
* `gammaBasis_palindromic` — each basis element is palindromic about `n/2`;
* `IsGammaPositive.palindromic` — **γ-positivity implies palindromicity** (symmetry
  of the coefficient sequence), the structural constraint underlying every
  `h*`-polynomial of a symmetric edge polytope;
* `IsGammaPositive.coeff_nonneg` — γ-positive polynomials have nonnegative
  coefficients.

## Reference frame

The catalog entries `ohsugi-tsuchiya-conj`, `higashitani-jochemko-michalek`, `gal`
and `branden-gamma` concern precisely the γ-positivity of these Ehrhart
`h*`-polynomials; the phenomenon that palindromicity is *necessary but not
sufficient* for γ-positivity is what makes the "minimal dimension 36" question
nontrivial (see `GammaPositivityCounterexample.lean`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): γ-positivity is a strict strengthening of palindromicity;
every γ-positive polynomial is palindromic and has nonnegative, unimodal coefficients,
but the converse fails already in very small degree.
Experiment (Experimenter): computed the coefficient vectors of `t^i(1+t)^(n-2i)` for
small `n`; each is a shifted binomial row, symmetric about `n/2`.
Analysis (Analyst): the symmetry `C(n-2i,k-i)=C(n-2i,(n-2i)-(k-i))` is the engine;
nonnegativity is immediate; unimodality needs the same-center superposition argument.
Critique (Critic): must guard `k ≤ n` for palindromicity, else Nat subtraction
`n - k` collapses to `0` and the identity is false.
Synthesis: the coefficient formula `gammaBasis_coeff` reduces both structural
theorems to binomial identities.
-/

open GammaPositivity

open Polynomial BigOperators

theorem GammaPositivity.gammaBasis_coeff(n i k : ℕ) :
    (gammaBasis n i).coeff k =
      if i ≤ k then ((n - 2 * i).choose (k - i) : ℝ) else 0 := by sorry
