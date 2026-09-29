-- Prove2me | solution 1 for ForkPinning.injective_lift_iff_ker_eq_commutator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:38:30.707801+00:00
-- url     : https://prove2.me/submissions/8c2219b8-a69e-4e97-b9e3-f43149a565be

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

/-- Every element of the abelianization is the class of a group element. -/
lemma exists_abelianization_of {G : Type*} [Group G] (x : Abelianization G) :
    ∃ g : G, Abelianization.of g = x := by
  induction x using QuotientGroup.induction_on with
  | H g => exact ⟨g, rfl⟩


variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {A : Type*} [CommGroup A] [Fintype A] [DecidableEq A]
variable [Fintype (Abelianization G)] [DecidableEq (Abelianization G)]





/-! ## The Jacobi sign is a minimal conductor for the `S₃` closure -/



open ForkPinning in
omit [Fintype G] [Nonempty G] [DecidableEq G] [Fintype A] [DecidableEq A]
  [Fintype (Abelianization G)] [DecidableEq (Abelianization G)] in
theorem solution(f : G →* A) :
    Function.Injective (Abelianization.lift f) ↔ ∀ g : G, f g = 1 → g ∈ commutator G := by
  constructor
  · intro h g hg
    have hx : Abelianization.lift f (Abelianization.of g) = Abelianization.lift f 1 := by
      simpa using hg
    exact (QuotientGroup.eq_one_iff g).mp (h hx)
  · intro h
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨g, rfl⟩ := exists_abelianization_of x
    have hg : f g = 1 := by
      simpa using hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff g).mpr (h g hg)
