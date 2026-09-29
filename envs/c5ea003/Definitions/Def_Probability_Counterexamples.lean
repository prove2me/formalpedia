-- Prove2me | Definitions.Def_Probability_Counterexamples
-- name    : Probability_Counterexamples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:59.844442+00:00
-- url     : https://prove2.me/theorems/4791ac1a-7f91-4108-97b1-47f480028e0e
-- title:
--   Aether Catalog definitions — Probability_Counterexamples
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Counterexamples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Counterexamples.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_JacobianCore

/-!
# Counterexample candidates that *fail* the Jacobian hypothesis

A standard way researchers probe the Jacobian Conjecture is to write down a
plausible-looking non-triangular polynomial map and test whether its Jacobian
determinant is a nonzero constant.  If `det(JF)` is *not* constant, the map is
simply **not a candidate**: the hypothesis of the conjecture fails, and nothing
can be concluded (the map may or may not be injective).

This file makes that falsification precise for two famous "first guesses", and
verifies with zero sorries that each fails the constancy requirement.

## Main results

* `cand2_jacDet` / `cand2_jacDet_not_const` — the symmetric **degree-2** map
  `F(X₀,X₁) = (X₀+X₁², X₁+X₀²)` has `det(JF) = 1 - 4X₀X₁`, which is **not
  constant**.  Contrast with `DegreeTwo.lean`: the *triangular* degree-2 maps do
  satisfy the hypothesis, this non-triangular one does not.
* `cand3_jacDet` / `cand3_jacDet_not_const` — the symmetric **degree-3** map
  `F(X₀,X₁) = (X₀+X₁³, X₁+X₀³)` has `det(JF) = 1 - 9X₀²X₁²`, again **not
  constant**.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): the "obvious" symmetric maps `X_i + X_{σ(i)}^d` are
  *not* Jacobian-Conjecture counterexamples because they already fail the
  hypothesis — their Jacobian determinant is a nonconstant polynomial.  This is
  why genuine candidates must use *cubic-linear / nilpotent* structure
  (cf. `Druzkowski.lean`), not arbitrary monomials.
* Experiment (Experimenter): computed `det(JF)` with `pderiv` and proved
  non-constancy by evaluating the determinant polynomial at two points
  (`(0,0)` and `(1,1)`) that give different values; if it were `C c` both
  evaluations would equal `c`.
* Analysis (Analyst): the off-diagonal cross terms `∂F₀/∂X₁ · ∂F₁/∂X₀`
  (`= 4X₀X₁`, resp. `9X₀²X₁²`) are exactly what break constancy.  Nilpotency of
  the linear part (Drużkowski) is the structural device that kills precisely
  these cross terms, which is why it produces honest candidates while naive
  symmetry does not.
* Critique (Critic): we are *not* claiming these maps are non-injective or that
  they refute anything — only that they fail the conjecture's hypothesis, the
  correct and verifiable statement.  This guards against the common error of
  "testing the conjecture" on maps it never applied to.
* Synthesis (PI): the trilogy is complete — triangular degree-2 (holds),
  cubic-linear degree-3 witness (holds), naive symmetric candidates (excluded by
  hypothesis).  The boundary between "candidate" and "non-candidate" is the
  constancy of `det(JF)`, computed mechanically here.
-/

open MvPolynomial

namespace JacobianConjecture.Counterexamples

/-! ## Degree-2 symmetric (non-triangular) candidate -/

/-- `F(X₀,X₁) = (X₀ + X₁², X₁ + X₀²)`. -/
noncomputable def cand2 : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => X 0 + (X 1) ^ 2
  | 1 => X 1 + (X 0) ^ 2



/-! ## Degree-3 symmetric (non-triangular) candidate -/

/-- `F(X₀,X₁) = (X₀ + X₁³, X₁ + X₀³)`. -/
noncomputable def cand3 : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => X 0 + (X 1) ^ 3
  | 1 => X 1 + (X 0) ^ 3



end JacobianConjecture.Counterexamples


