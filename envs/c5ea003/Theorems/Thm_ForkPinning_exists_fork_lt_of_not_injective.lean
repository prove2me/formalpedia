-- Prove2me | Theorems.Thm_ForkPinning_exists_fork_lt_of_not_injective
-- name    : ForkPinning.exists_fork_lt_of_not_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:10.956491+00:00
-- url     : https://prove2.me/theorems/ce265464-7b7a-412b-a963-95284237fc7f
-- title:
--   Failure of injectivity is detected by a single coset fork.
-- statement:
--   **Failure of injectivity is detected by a single coset fork.**  If the induced map on the
--   abelianization is not injective, the indicator fork of one of the merged commutator cosets is
--   fully pinned by the abelianization but only partially by the character.
--
--   ```lean
--   theorem ForkPinning.exists_fork_lt_of_not_injective(f : G →* A)
--       (hinj : ¬ Function.Injective (Abelianization.lift f)) :
--       ∃ Y : G → Bool,
--         mutualInfo (fun g : G => Abelianization.of g) Y = H Y ∧
--         mutualInfo (fun g : G => f g) Y < mutualInfo (fun g : G => Abelianization.of g) Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningConductor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningConductor.lean#L69

-- Thm stub generated from Probability/ForkPinningConductor.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
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


omit [DecidableEq G] in

theorem ForkPinning.exists_fork_lt_of_not_injective(f : G →* A)
    (hinj : ¬ Function.Injective (Abelianization.lift f)) :
    ∃ Y : G → Bool,
      mutualInfo (fun g : G => Abelianization.of g) Y = H Y ∧
      mutualInfo (fun g : G => f g) Y < mutualInfo (fun g : G => Abelianization.of g) Y := by sorry
