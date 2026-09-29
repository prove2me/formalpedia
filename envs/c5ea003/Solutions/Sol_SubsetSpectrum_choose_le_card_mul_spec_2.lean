-- Prove2me | solution 2 for SubsetSpectrum.choose_le_card_mul_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:14:47.727932+00:00
-- url     : https://prove2.me/submissions/06270f80-e977-4fe9-953c-a42bdf4e3604

-- Thm stub generated from Applications/ActionSpectrum/Basic.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic

/-!
# The subset spectrum of a finite group action

For a finite group `G` acting on a finite set `X` (`n := |X|`) the **subset spectrum**
is the sequence

`t_r := ` number of `G`-orbits on the `r`-element subsets of `X`,   `0 ≤ r ≤ n`.

This is the classical sequence of a permutation group (Livingstone–Wagner, Cameron).
This file sets up a *computable* model of the spectrum (`SubsetSpectrum.spec`) built from
`Finset.powersetCard` and orbit `Finset`s, and establishes its basic structural theory:

* `SubsetSpectrum.spec_zero`, `SubsetSpectrum.spec_card` : the two boundary values are `1`;
* `SubsetSpectrum.spec_pos`, `SubsetSpectrum.spec_eq_zero_of_lt` : support of the spectrum;
* `SubsetSpectrum.spec_compl` : the complementation symmetry `t_r = t_{n-r}`;
* `SubsetSpectrum.spec_le_choose` and `SubsetSpectrum.choose_le_card_mul_spec` :
  the two-sided sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)`;
* `SubsetSpectrum.spec_of_trivial_action` : for the trivial action `t_r = C(n,r)`;
* `SubsetSpectrum.spec_eq_one_iff` : `t_r = 1` is exactly `r`-homogeneity, and
  `SubsetSpectrum.spec_one_eq_one_iff_pretransitive` : `t_1 = 1` is exactly transitivity;
* `SubsetSpectrum.spec_perm_eq_one` : the symmetric group is set-transitive;
* `Nat.choose_mul_choose_le_choose_sq` : log-concavity of the binomial coefficients
  (proved from scratch — Mathlib has no log-concavity API).

The log-concavity question itself is treated in `Applications.ActionSpectrum.LogConcavity`.
-/

open Finset

/-! ## Log-concavity of binomial coefficients -/


open SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-! ## The induced action on finite subsets -/










variable [Fintype G]






variable [Fintype X]

/-! ## Boundary values and support -/





/-! ## The sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace SSWB

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]

theorem mem_orb_self (s : Finset X) : s ∈ orb G s := by
  rw [orb, Finset.mem_image]
  exact ⟨1, Finset.mem_univ 1, act_one s⟩

theorem choose_le_card_mul_spec (r : ℕ) :
    (Fintype.card X).choose r ≤ Fintype.card G * spec G X r := by
  classical
  have hcard : ((univ : Finset X).powersetCard r).card = (Fintype.card X).choose r := by
    rw [Finset.card_powersetCard, Finset.card_univ]
  rw [← hcard]
  show ((univ : Finset X).powersetCard r).card
    ≤ Fintype.card G * (((univ : Finset X).powersetCard r).image (orb G)).card
  refine Finset.card_le_mul_card_image _ _ ?_
  intro a ha
  obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 ha
  refine le_trans (Finset.card_le_card (t := orb G x₀) ?_) ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hxx : x ∈ orb G x := mem_orb_self x
    rw [hx.2] at hxx
    exact hxx
  · rw [orb]
    exact le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

end SSWB

theorem solution (r : ℕ) :
    (Fintype.card X).choose r ≤ Fintype.card G * spec G X r :=
  SSWB.choose_le_card_mul_spec r
