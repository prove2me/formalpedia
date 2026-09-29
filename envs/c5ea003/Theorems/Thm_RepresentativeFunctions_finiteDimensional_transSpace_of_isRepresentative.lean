-- Prove2me | Theorems.Thm_RepresentativeFunctions_finiteDimensional_transSpace_of_isRepresentative
-- name    : RepresentativeFunctions.finiteDimensional_transSpace_of_isRepresentative
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:29.21297+00:00
-- url     : https://prove2.me/theorems/1d19ae7a-fc80-4019-87c8-b6904b8bc719
-- title:
--   If `f` is representative then its translates span a finite dimensional space:
-- statement:
--   If `f` is representative then its translates span a finite dimensional space:
--   this is the finiteness of the rank of the Hankel matrix of `f`.
--
--   ```lean
--   theorem RepresentativeFunctions.finiteDimensional_transSpace_of_isRepresentative{f : List X → K}
--       (hf : IsRepresentative f) : FiniteDimensional K (transSpace f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/RepresentativeFunctions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/RepresentativeFunctions.lean#L102

-- Thm stub generated from Novelty/RepresentativeFunctions.lean
import Mathlib
import Definitions.Def_Novelty_RepresentativeFunctions
/-
# Representative functions on a free monoid and the Kleene–Schützenberger theorem

Following *Various bialgebras of representative functions on free monoids*, a function
`f : X* → K` is **representative** when its "coproduct" factors through a finite tensor:
`f(uv) = Σ_{i<n} g_i(u) h_i(v)`.  Its **graph** is the noncommutative series
`Σ_w f(w) w`, and the Kleene–Schützenberger theorem identifies representative functions
with the series admitting a **linear representation** `f(w) = λ μ(w) γ`, where
`μ : X* → M_n(K)` is a monoid morphism.

This file proves the full equivalence, in the form of a three-way cycle:

* `IsRepresentative f → FiniteDimensional K (transSpace f)`
  (`finiteDimensional_transSpace_of_isRepresentative`);
* `FiniteDimensional K (transSpace f) → HasLinearRep f`
  (`hasLinearRep_of_finiteDimensional`) — the Myhill–Nerode / Hankel-rank construction:
  the space spanned by the left translates of `f` is stable under the shift operators,
  and reading these operators in a basis produces the representation;
* `HasLinearRep f → IsRepresentative f` (`isRepresentative_of_hasLinearRep`).

The resulting `tfae` statement `representative_tfae` is the Kleene–Schützenberger
equivalence in the "representative function" formulation used by the paper.

We also prove the closure properties which make the representative functions a
subalgebra of `K^{X*}`: they are closed under scalar multiples, sums and the Hadamard
(pointwise) product, the latter through the tensor product of linear representations.
-/

open RepresentativeFunctions

variable {X K : Type*} [Field K]

/-! ## Translates -/




/-! ## Representative functions and linear representations -/







/-! ## Linear representation ⟹ representative -/


/-! ## Representative ⟹ finite dimensional Hankel space -/

theorem RepresentativeFunctions.finiteDimensional_transSpace_of_isRepresentative{f : List X → K}
    (hf : IsRepresentative f) : FiniteDimensional K (transSpace f) := by sorry
