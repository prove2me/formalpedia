-- Prove2me | Definitions.Def_Novelty_RepresentativeFunctions
-- name    : Novelty_RepresentativeFunctions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:39:26.994314+00:00
-- url     : https://prove2.me/theorems/4a173c52-2daf-4706-b3f0-fa72385b0d2e
-- title:
--   Aether Catalog definitions — Novelty_RepresentativeFunctions
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RepresentativeFunctions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RepresentativeFunctions.lean by skeleton subtraction
import Mathlib
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

namespace RepresentativeFunctions

variable {X K : Type*} [Field K]

/-! ## Translates -/

/-- The left translate `w⁻¹f : u ↦ f(wu)`. -/
def ltrans (w : List X) (f : List X → K) : List X → K := fun u => f (w ++ u)

/-- The linear span of all left translates of `f` (the "Hankel space" of `f`). -/
def transSpace (f : List X → K) : Submodule K (List X → K) :=
  Submodule.span K (Set.range fun w => ltrans w f)


/-! ## Representative functions and linear representations -/

/-- `f` is *representative*: the function `(u,v) ↦ f(uv)` is a finite sum of products of
functions of `u` and of `v`. -/
def IsRepresentative (f : List X → K) : Prop :=
  ∃ (n : ℕ) (g h : Fin n → (List X → K)), ∀ u v : List X, f (u ++ v) = ∑ i, g i u * h i v

/-- The multiplicative extension `μ : X* → M_n(K)` of a matrix-valued map on letters. -/
def mword {n : ℕ} (mu : X → Matrix (Fin n) (Fin n) K) : List X → Matrix (Fin n) (Fin n) K
  | [] => 1
  | a :: w => mu a * mword mu w




/-- `f` admits a *linear representation* of some dimension `n`: `f(w) = λ μ(w) γ`. -/
def HasLinearRep (f : List X → K) : Prop :=
  ∃ (n : ℕ) (lam : Fin n → K) (mu : X → Matrix (Fin n) (Fin n) K) (gam : Fin n → K),
    ∀ w, f w = ∑ i, ∑ j, lam i * mword mu w i j * gam j

/-! ## Linear representation ⟹ representative -/


/-! ## Representative ⟹ finite dimensional Hankel space -/


/-! ## Finite dimensional Hankel space ⟹ linear representation -/


/-! ## The Kleene–Schützenberger equivalence -/


/-! ## The algebra of representative functions -/






end RepresentativeFunctions


