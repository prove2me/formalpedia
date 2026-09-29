-- Prove2me | solution 1 for A4ForkPinning.factorsThroughAb_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:03:16.774168+00:00
-- url     : https://prove2.me/submissions/3e49ff69-a95d-4320-9081-ec2de802110d

-- Sol generated from Algebra/A4ForkPinning/Unpinnable.lean
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




/-! ## `A₄`: the `V₄`-fork factors, the identity fork does not -/







/-! ## `A₅`: absolutely unpinnable -/










open A4ForkPinning in
theorem solution(F : G → Prop) :
    FactorsThroughAb F ↔ ∀ g c, c ∈ commutator G → (F (g * c) ↔ F g) := by
  constructor
  · rintro ⟨f, hf⟩ g c hc
    have hc1 : Abelianization.of c = 1 :=
      MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker _ hc)
    rw [hf, hf, map_mul, hc1, mul_one]
  · intro h
    refine ⟨fun x => ∃ g, Abelianization.of g = x ∧ F g, fun g => ⟨fun hg => ⟨g, rfl, hg⟩, ?_⟩⟩
    rintro ⟨g', hg', hF⟩
    have hmem : g'⁻¹ * g ∈ commutator G := QuotientGroup.eq.1 hg'
    have := h g' (g'⁻¹ * g) hmem
    rw [show g' * (g'⁻¹ * g) = g by group] at this
    exact this.2 hF
