-- Prove2me | Definitions.Def_Probability_Druzkowski
-- name    : Probability_Druzkowski
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:27.746449+00:00
-- url     : https://prove2.me/theorems/21ddb660-a924-4f2d-90f0-ba57be26f991
-- title:
--   Aether Catalog definitions — Probability_Druzkowski
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Druzkowski`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Druzkowski.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_JacobianCore

/-!
# A verified degree-3 Druzkowski cubic-linear automorphism

Drużkowski (1983) proved that the full Jacobian Conjecture reduces to maps of the
special **cubic-linear** form
`F_i = X_i + (∑_j a_{ij} X_j)^3`,
where the linear forms appearing are cubed.  The reduction does not lower the
dimension, but it pins the nonlinear part to be a sum of cubes of linear forms,
and the Jacobian condition becomes the statement that the matrix
`A = (a_{ij})` gives a *nilpotent* Jacobian `J(H) = 3·diag((Ax)^2)·A`.

Here we construct and **fully verify** an explicit non-triangular instance of a
Drużkowski map in dimension 2:

`F(X₀,X₁) = (X₀ + (X₀-X₁)³, X₁ + (X₀-X₁)³)`,

coming from the rank-one nilpotent matrix `A = !![1,-1;1,-1]` (note `A² = 0`).
This is genuinely *not* a triangular shear: both coordinates are modified by the
same nonlinear term.

## Main results

* `druzkowski_isPolyAut` — `F` is a polynomial automorphism with the explicit
  polynomial inverse `G(X₀,X₁) = (X₀ - (X₀-X₁)³, X₁ - (X₀-X₁)³)`.
* `druzkowski_bijective` — consequently `F` induces a bijection on every
  `ℚ`-algebra (via the Core bridge theorem), so the conjecture *holds* for this
  map.
* `druzkowski_jacDet` — `det(JF) = 1`, a nonzero constant: the hypothesis of the
  Jacobian Conjecture is satisfied.
* `druzkowski_nilpotent` — the Jacobian of the cubic part `H` squares to `0`,
  the structural nilpotency at the heart of Drużkowski's reduction.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): the cubic-linear normal form is not a curiosity —
  one can *write down* honest non-triangular automorphisms in it.  Conjecture:
  for the rank-one nilpotent `A = !![1,-1;1,-1]`, the cubic-linear map is an
  automorphism with constant Jacobian, witnessing the Jacobian Conjecture in
  Drużkowski form.
* Experiment (Experimenter): chose the cube of the single linear form `X₀-X₁`.
  Because `F₀ - F₁ = X₀ - X₁` is preserved, the inverse is forced to be
  `G = X - (X₀-X₁)³` componentwise.  `IsPolyAut` was discharged by `ring` after
  `aeval`-substitution; `jacDet` and nilpotency by `pderiv` + `ring`.
* Analysis (Analyst): the key invariant is the *linear form is fixed by F*:
  `(X₀-X₁) ∘ F = X₀-X₁`, which makes the cubic term constant along the inversion
  and turns the cubic-linear inversion into a linear back-substitution.  This is
  exactly why nilpotency of `A` (here `A²=0`) controls invertibility.
* Critique (Critic): is this "too special"?  Yes — it is one map, not the
  reduction theorem.  But it is a *bona fide* non-triangular cubic-linear
  automorphism with all four predicted properties verified with zero sorries,
  refuting any suspicion that the cubic-linear class is empty of interesting
  examples.  The general Drużkowski reduction remains open to formalization
  (see FUTURE_DIRECTIONS).
* Synthesis (PI): combined with `DegreeTwo.lean` (triangular degree-2 family)
  and `Counterexamples.lean` (candidates that *fail* the constancy hypothesis),
  this gives a three-point spread: degree-2 holds, degree-3 cubic-linear holds
  for this witness, and naive degree-3 candidates fail the hypothesis.
-/

open MvPolynomial

namespace JacobianConjecture.Druzkowski

/-- The Drużkowski cubic-linear map `F(X₀,X₁) = (X₀+(X₀-X₁)³, X₁+(X₀-X₁)³)`. -/
noncomputable def F : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => X 0 + (X 0 - X 1) ^ 3
  | 1 => X 1 + (X 0 - X 1) ^ 3

/-- The explicit polynomial inverse `G(X₀,X₁) = (X₀-(X₀-X₁)³, X₁-(X₀-X₁)³)`. -/
noncomputable def G : Fin 2 → MvPolynomial (Fin 2) ℚ
  | 0 => X 0 - (X 0 - X 1) ^ 3
  | 1 => X 1 - (X 0 - X 1) ^ 3




/-- The cubic (nonlinear) part `H` of `F`, here `H₀ = H₁ = (X₀-X₁)³`. -/
noncomputable def H : Fin 2 → MvPolynomial (Fin 2) ℚ := fun _ => (X 0 - X 1) ^ 3


end JacobianConjecture.Druzkowski


