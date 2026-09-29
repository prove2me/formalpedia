-- Prove2me | Definitions.Def_Probability_GammaPositivityCounterexample
-- name    : Probability_GammaPositivityCounterexample
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:32.972506+00:00
-- url     : https://prove2.me/theorems/7457d962-8541-4a13-a73b-516d829d6389
-- title:
--   Aether Catalog definitions — Probability_GammaPositivityCounterexample
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GammaPositivityCounterexample`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GammaPositivityCounterexample.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_GammaPositivity

/-!
# Palindromicity does not imply γ-positivity

The catalog question on the *minimal dimension of a non-γ-positive symmetric edge
polytope* rests on one fundamental phenomenon: an Ehrhart `h*`-polynomial is always
**palindromic** (its coefficient sequence is symmetric), yet palindromicity by itself
is *not enough* to guarantee **γ-positivity**.  The whole difficulty of pinning the
minimal dimension at `36` comes from this gap.

Here we make the gap concrete and machine-checked in the smallest possible degrees:

* `gammaPositive_one_add_X_pow` — the "trivial" `h*`-polynomial `(1+t)^n` is γ-positive;
* `one_add_Xsq_palindromic` / `one_add_Xsq_not_gammaPositive` — the palindromic
  polynomial `1 + t²` is **not** γ-positive (it even fails unimodality);
* `flat4_palindromic` / `flat4_unimodal` / `flat4_not_gammaPositive` — the polynomial
  `1 + t + t² + t³ + t⁴` is palindromic **and** unimodal with nonnegative
  coefficients, yet still fails γ-positivity.

The last example is the sharp one: it possesses *every* necessary consequence of
γ-positivity established in `GammaPositivity.lean` (nonnegativity, symmetry, and
unimodality) and nevertheless is not γ-positive — exactly the behaviour that a
minimal non-γ-positive symmetric edge polytope must exhibit, only realised here in
degree `4` instead of `36`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): if palindromicity implied γ-positivity, the "minimal
dimension" question would be vacuous. Conjecture: the implication fails in low degree.
Experiment (Experimenter): solved the linear γ-systems by hand.  For `1+t²` (order 2):
`γ₀ = 1`, `2γ₀ + γ₁ = 0 ⟹ γ₁ = -2 < 0`.  For `1+t+t²+t³+t⁴` (order 4):
`γ₀ = 1`, `4γ₀ + γ₁ = 1 ⟹ γ₁ = -3 < 0`.
Analysis (Analyst): the obstruction is purely the *sign* of the second γ-coefficient;
reading off `coeff 0` and `coeff 1` of the γ-expansion already forces a contradiction.
Critique (Critic): `1+t²` is not unimodal, so it is a "cheap" counterexample; we add
`1+t+t²+t³+t⁴`, which is unimodal, nonnegative and palindromic, to show the failure is
genuine and not an artefact of non-unimodality.
Synthesis: palindromic ⊋ γ-positive already in degree 2, and the separation persists
among unimodal polynomials from degree 4 onward.
-/

namespace GammaPositivity

open Polynomial BigOperators


/-! ### First separation: `1 + t²` (degree 2, not even unimodal) -/



/-! ### Sharp separation: `1 + t + t² + t³ + t⁴` (degree 4, unimodal) -/

/-- The flat symmetric polynomial `1 + t + t² + t³ + t⁴`. -/
noncomputable def flat4 : ℝ[X] := 1 + X + X ^ 2 + X ^ 3 + X ^ 4




end GammaPositivity


