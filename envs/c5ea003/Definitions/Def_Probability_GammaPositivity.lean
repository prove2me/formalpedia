-- Prove2me | Definitions.Def_Probability_GammaPositivity
-- name    : Probability_GammaPositivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:20.18385+00:00
-- url     : https://prove2.me/theorems/ec2abf34-54b4-4658-bcdd-7b276a9fd1b7
-- title:
--   Aether Catalog definitions — Probability_GammaPositivity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GammaPositivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GammaPositivity.lean by skeleton subtraction
import Mathlib

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

namespace GammaPositivity

open Polynomial BigOperators

/-- The `i`-th element of the γ-basis in order `n`: `t^i (1+t)^(n-2i)`. -/
noncomputable def gammaBasis (n i : ℕ) : ℝ[X] := (1 + X) ^ (n - 2 * i) * X ^ i





/-- A polynomial is **γ-positive of order `n`** if it is a nonnegative real
combination of the γ-basis elements `t^i (1+t)^(n-2i)` for `0 ≤ i ≤ ⌊n/2⌋`. -/
def IsGammaPositive (n : ℕ) (p : ℝ[X]) : Prop :=
  ∃ γ : ℕ → ℝ, (∀ i, 0 ≤ γ i) ∧
    p = ∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * gammaBasis n i

/-- A polynomial is **palindromic of order `n`** if its coefficient sequence is
symmetric under `k ↦ n - k` on `{0, …, n}`. -/
def IsPalindromic (n : ℕ) (p : ℝ[X]) : Prop := ∀ k ≤ n, p.coeff k = p.coeff (n - k)



end GammaPositivity


