-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Unpinnable
-- name    : Algebra_A4ForkPinning_Unpinnable
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:33.98758+00:00
-- url     : https://prove2.me/theorems/bc1920fc-a873-418c-9a87-1cec30f892d1
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Unpinnable
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Unpinnable`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Unpinnable.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
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

namespace A4ForkPinning

open Equiv Equiv.Perm

/-! ## The criterion -/

variable {G : Type*} [Group G]

/-- A fork `F : G → Prop` *factors through the abelianisation* if it is the pullback
of a predicate on `G^ab`.  By class field theory this is precisely the class of
forks that a congruence condition on `p` can detect. -/
def FactorsThroughAb (F : G → Prop) : Prop :=
  ∃ f : Abelianization G → Prop, ∀ g, F g ↔ f (Abelianization.of g)



/-! ## `A₄`: the `V₄`-fork factors, the identity fork does not -/


/-- An explicit non-trivial element of `V₄`: the double transposition `(01)(23)`. -/
def dbl : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3





/-! ## `A₅`: absolutely unpinnable -/

/-- Two non-commuting even permutations of `Fin 5`. -/
def a5x : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- A second one, chosen to move the support of `a5x`. -/
def a5y : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4







end A4ForkPinning


