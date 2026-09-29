-- Prove2me | solution 1 for ForkPinning.exists_fork_lt_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:40:43.413041+00:00
-- url     : https://prove2.me/submissions/616969a1-da56-4dd4-9114-0f834a863066

-- Sol generated from Probability/ForkPinningConductor.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningDataProcessing
import Theorems.Thm_ForkPinning_mutualInfo_lt_entropy_of_not_determines
import Theorems.Thm_ForkPinning_pinned_iff_determines
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
omit [DecidableEq G] in
theorem solution(f : G →* A)
    (hinj : ¬ Function.Injective (Abelianization.lift f)) :
    ∃ Y : G → Bool,
      mutualInfo (fun g : G => Abelianization.of g) Y = H Y ∧
      mutualInfo (fun g : G => f g) Y < mutualInfo (fun g : G => Abelianization.of g) Y := by
  simp only [Function.Injective, not_forall] at hinj
  obtain ⟨a, b, hab, hne⟩ := hinj
  obtain ⟨ga, hga⟩ := exists_abelianization_of a
  obtain ⟨gb, hgb⟩ := exists_abelianization_of b
  refine ⟨fun g => decide (Abelianization.of g = a), ?_, ?_⟩
  · -- the abelianization determines the coset indicator, hence pins it completely
    refine (pinned_iff_determines _ _).mpr ?_
    intro w w' hw
    simp [hw]
  · -- but the character cannot distinguish the two merged cosets
    have hdet : ¬ Determines (fun g : G => f g) (fun g => decide (Abelianization.of g = a)) := by
      intro hdet
      have hfa : f ga = f gb := by
        have h1 : Abelianization.lift f (Abelianization.of ga) = f ga :=
          Abelianization.lift_apply_of f ga
        have h2 : Abelianization.lift f (Abelianization.of gb) = f gb :=
          Abelianization.lift_apply_of f gb
        rw [← h1, ← h2, hga, hgb, hab]
      have h := hdet ga gb hfa
      simp only [hga, hgb, decide_eq_decide] at h
      exact hne (h.mp trivial).symm
    have hpin : mutualInfo (fun g : G => Abelianization.of g)
        (fun g => decide (Abelianization.of g = a)) = H (fun g : G => decide
          (Abelianization.of g = a)) := by
      refine (pinned_iff_determines _ _).mpr ?_
      intro w w' hw
      simp [hw]
    rw [hpin]
    exact mutualInfo_lt_entropy_of_not_determines _ _ hdet
