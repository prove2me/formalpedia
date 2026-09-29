-- Prove2me | solution 1 for A4ForkPinning.commutator_alternating_five_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:05:17.14997+00:00
-- url     : https://prove2.me/submissions/fcceec80-444f-4b3a-8d86-8e8752ab2cb1

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



theorem a5x_even : Equiv.Perm.sign a5x = 1 := by decide

theorem a5y_even : Equiv.Perm.sign a5y = 1 := by decide

theorem a5_noncomm : a5x * a5y ≠ a5y * a5x := by decide





open A4ForkPinning in
theorem solution:
    commutator (alternatingGroup (Fin 5)) = ⊤ := by
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5)))
    (by infer_instance)) with h | h
  · exfalso
    have hcenter := (commutator_eq_bot_iff_center_eq_top _).1 h
    have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
      intro a b
      have hb : b ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [hcenter]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.1 hb a
    exact a5_noncomm (congrArg Subtype.val
      (hcomm ⟨a5x, mem_alternatingGroup.2 a5x_even⟩ ⟨a5y, mem_alternatingGroup.2 a5y_even⟩))
  · exact h
