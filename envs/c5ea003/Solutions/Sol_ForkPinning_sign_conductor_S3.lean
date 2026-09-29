-- Prove2me | solution 1 for ForkPinning.sign_conductor_S3
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:55.074874+00:00
-- url     : https://prove2.me/submissions/68f1f012-5f09-4e96-b311-2c89344f6b44

-- Sol generated from Probability/ForkPinningConductor.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningDataProcessing
/-
# The conductor of a fork: equality in data processing detects the character's kernel

`ForkPinningDataProcessing` proves that no abelian character `f : G →* A` of the Galois group
can carry more information about a fork than the abelianization map `G → G^ab`, and that an
*injective* induced map `φ = Abelianization.lift f` loses nothing.  This file closes the
converse — conjecture **C8** of `FUTURE_DIRECTIONS.md` — and thereby characterises the
*conductor* of the abelian congruence data:

> a character `f` is as informative as the full abelianization **for every fork** exactly when
> `ker f = [G,G]`, i.e. exactly when `φ` is injective; otherwise there is an explicit fork
> (the indicator of a single commutator coset) on which `f` is *strictly* worse.

Main results:

* `ForkPinning.injective_lift_iff_ker_eq_commutator` : `φ` is injective iff the kernel of the
  character is exactly the commutator subgroup.
* `ForkPinning.exists_fork_lt_of_not_injective` : if `φ` is **not** injective there is a fork
  (a coset indicator) with `I(f ; Y) < I(G^ab ; Y)`; in fact `I(G^ab ; Y) = H Y`, so the loss
  is the whole of the fork's entropy.
* `ForkPinning.mutualInfo_eq_abelianization_forall_iff` : the two-sided criterion
  `(∀ Y, I(f ; Y) = I(G^ab ; Y)) ↔ Function.Injective φ`.
* `ForkPinning.sign_conductor_S3` : the sign character of `S₃` has kernel exactly the
  commutator subgroup, hence is a *minimal-conductor* observable: it already extracts all the
  abelian information of every fork of the `S₃` closure.  This is the exact formal counterpart
  of the measured statement "the congruence content of the `x³+x+1` fork is entirely the
  Jacobi sign".
-/


open ForkPinning

open Finset Real
open scoped commutatorElement



variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
variable [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]





/-! ## The Jacobi sign is a minimal conductor for the `S₃` closure -/



open ForkPinning in
theorem solution:
    ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → σ ∈ commutator (Equiv.Perm (Fin 3)) := by
  have hc : ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆ ∈
      commutator (Equiv.Perm (Fin 3)) := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have henum : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 →
      σ = 1 ∨ σ = ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆ ∨
        σ = ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆ *
          ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆ := by decide
  intro σ hσ
  rcases henum σ hσ with h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hc
  · rw [h]; exact mul_mem hc hc
