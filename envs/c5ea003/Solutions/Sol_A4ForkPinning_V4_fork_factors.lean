-- Prove2me | solution 1 for A4ForkPinning.V4_fork_factors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:05:13.515726+00:00
-- url     : https://prove2.me/submissions/b8789523-120c-4edd-ae4a-51f89494b3ad

-- Sol generated from Algebra/A4ForkPinning/Unpinnable.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_GroupA4
import Definitions.Def_Algebra_A4ForkPinning_Unpinnable
import Theorems.Thm_A4ForkPinning_factorsThroughAb_iff
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




/-! ## `A₄`: the `V₄`-fork factors, the identity fork does not -/







/-! ## `A₅`: absolutely unpinnable -/










open A4ForkPinning in
theorem solution:
    FactorsThroughAb (fun g : alternatingGroup (Fin 4) => (g : Equiv.Perm (Fin 4)) ∈ V4) := by
  rw [factorsThroughAb_iff]
  intro g c hc
  have hcV : (c : Equiv.Perm (Fin 4)) ∈ V4 := by
    rw [commutator_alternatingGroup] at hc
    exact hc
  constructor
  · intro hgc
    have : (g : Equiv.Perm (Fin 4)) = ((g * c : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
        * (c : Equiv.Perm (Fin 4))⁻¹ := by
      push_cast; group
    rw [this]
    exact V4.mul_mem hgc (V4.inv_mem hcV)
  · intro hg
    have : ((g * c : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
        = (g : Equiv.Perm (Fin 4)) * (c : Equiv.Perm (Fin 4)) := rfl
    rw [this]
    exact V4.mul_mem hg hcV
