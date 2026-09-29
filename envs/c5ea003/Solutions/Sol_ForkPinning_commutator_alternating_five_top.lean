-- Prove2me | solution 1 for ForkPinning.commutator_alternating_five_top
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:02:15.646834+00:00
-- url     : https://prove2.me/submissions/5288ff51-e631-4f53-b07f-cbfc119facf3

-- Sol generated from Probability/ForkPinningPerfect.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
/-
# Perfect Galois groups: total congruence blindness

The fork-pinning criterion has an extreme end.  If the Galois group of the closure is **perfect**
(`G = [G,G]`, e.g. `A₅`), then it has no non-trivial abelian character at all, so *no* fork of the
corresponding field carries a single bit of congruence information — the splitting behaviour is
completely invisible to Dirichlet characters.

* `ForkPinning.hom_trivial_of_commutator_top` — a perfect group has only the trivial character.
* `ForkPinning.perfect_all_flat` — every fork is flat for every abelian character.
* `ForkPinning.perfect_pinned_imp_entropy_zero` — a pinned fork must have zero entropy.
* `ForkPinning.commutator_alternating_five_top` / `ForkPinning.A5_all_forks_flat` — the
  instantiation to `A₅`, the Galois group of a generic quintic with square discriminant.
-/


open ForkPinning

open Finset Real
open scoped commutatorElement


variable {G : Type*} [Group G] [Fintype G] [Nonempty G]
variable {A β : Type*} [CommGroup A] [Fintype A] [DecidableEq A] [Fintype β] [DecidableEq β]





/-! ## The instantiation: `A₅` -/




open ForkPinning in
theorem solution: commutator (alternatingGroup (Fin 5)) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5)))
      inferInstance with hb | ht
  · exfalso
    have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
      intro a b
      have hmem : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 5)) := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [hb, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one] at hmem
      calc a * b = (a * b * a⁻¹) * a := by group
        _ = b * a := by rw [hmem]
    have ha : Equiv.swap (0 : Fin 5) 1 * Equiv.swap (1 : Fin 5) 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hb2 : Equiv.swap (2 : Fin 5) 3 * Equiv.swap (3 : Fin 5) 4 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hkey := hcomm ⟨_, ha⟩ ⟨_, hb2⟩
    rw [Subtype.ext_iff] at hkey
    simp only [Subgroup.coe_mul] at hkey
    have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (1 : Fin 5) 2) *
        (Equiv.swap (2 : Fin 5) 3 * Equiv.swap (3 : Fin 5) 4)
        ≠ (Equiv.swap (2 : Fin 5) 3 * Equiv.swap (3 : Fin 5) 4) *
          (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (1 : Fin 5) 2) := by decide
    exact hne hkey
  · exact ht
