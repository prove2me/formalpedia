-- Prove2me | Theorems.Thm_A4ForkPinning_factorsThroughAb_iff
-- name    : A4ForkPinning.factorsThroughAb_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:22:48.968438+00:00
-- url     : https://prove2.me/theorems/07cb3dbb-6a2d-47ff-8f44-297042d5af4a
-- title:
--   The pinning-content criterion.
-- statement:
--   **The pinning-content criterion.**  A fork factors through `G^ab` exactly when it
--   is invariant under multiplication by commutators.
--
--   ```lean
--   theorem A4ForkPinning.factorsThroughAb_iff(F : G → Prop) :
--       FactorsThroughAb F ↔ ∀ g c, c ∈ commutator G → (F (g * c) ↔ F g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/Unpinnable.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/Unpinnable.lean#L38

-- Thm stub generated from Algebra/A4ForkPinning/Unpinnable.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
import Definitions.Def_Algebra_A4ForkPinning_Unpinnable
/-
# The pinning-content criterion, and absolutely unpinnable fields

The experiments of papers 65–75 all instantiate one structural statement: a
binary splitting fork is congruence-pinned **iff it factors through the
abelianisation of the Galois group** (Takagi: congruence conditions on `p` see
the Frobenius only through abelian quotients).  This file proves that criterion
in the form of a purely group-theoretic equivalence, and then reads off the two
extreme entries of the pinning-content table.

* `A4ForkPinning.FactorsThroughAb` — a fork factors through `G^ab`;
* `A4ForkPinning.factorsThroughAb_iff` — **the criterion**: `F` factors through
  `G^ab` iff `F` is invariant under translation by commutators;
* `A4ForkPinning.V4_fork_factors` — the `A₄` fork `F₀ = [σ ∈ V₄]` *does* factor
  (this is why it is pinned, by a **cubic** character since `|A₄^ab| = 3`);
* `A4ForkPinning.identity_fork_not_factors` — the finer fork `F₁ = [σ = e]` does
  **not** factor: no modulus whatsoever can pin it (it can only leak);
* `A4ForkPinning.commutator_alternating_five_eq_top` — `A₅` is perfect, and
* `A4ForkPinning.A5_absolutely_unpinnable`,
  `A4ForkPinning.A5_fork_factors_iff_constant` — over an `A₅`-field **every**
  non-trivial fork is absolutely unpinnable: the predicted last line of the table.
-/

open A4ForkPinning

open Equiv Equiv.Perm

/-! ## The criterion -/

variable {G : Type*} [Group G]

theorem A4ForkPinning.factorsThroughAb_iff(F : G → Prop) :
    FactorsThroughAb F ↔ ∀ g c, c ∈ commutator G → (F (g * c) ↔ F g) := by sorry
