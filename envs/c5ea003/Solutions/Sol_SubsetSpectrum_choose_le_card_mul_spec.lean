-- Prove2me | solution 1 for SubsetSpectrum.choose_le_card_mul_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:21:36.519296+00:00
-- url     : https://prove2.me/submissions/e0468259-9133-4396-8c81-e0c418a90269

-- Sol generated from Applications/ActionSpectrum/Basic.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Theorems.Thm_SubsetSpectrum_mem_orb_self

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


lemma orb_card_le (s : Finset X) : (orb G s).card ≤ Fintype.card G := by
  simpa [orb, Finset.card_univ] using
    Finset.card_image_le (s := (univ : Finset G)) (f := fun g : G => act g s)




variable [Fintype X]

/-! ## Boundary values and support -/





/-! ## The sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` -/



/-! ## Complementation symmetry -/




/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/





open SubsetSpectrum in
theorem solution(r : ℕ) :
    (Fintype.card X).choose r ≤ Fintype.card G * spec G X r := by
  set S := ((univ : Finset X).powersetCard r) with hS
  have hsub : S ⊆ (S.image (orb G)).biUnion id := by
    intro s hs
    simp only [Finset.mem_biUnion, Finset.mem_image, id]
    exact ⟨orb G s, ⟨s, hs, rfl⟩, mem_orb_self s⟩
  have h1 : S.card ≤ ((S.image (orb G)).biUnion id).card := Finset.card_le_card hsub
  have h2 : ((S.image (orb G)).biUnion id).card ≤ ∑ O ∈ S.image (orb G), O.card :=
    Finset.card_biUnion_le
  have h3 : ∑ O ∈ S.image (orb G), O.card ≤ ∑ _O ∈ S.image (orb G), Fintype.card G := by
    refine Finset.sum_le_sum ?_
    intro O hO
    simp only [Finset.mem_image] at hO
    obtain ⟨s, -, rfl⟩ := hO
    exact orb_card_le s
  have h4 : S.card = (Fintype.card X).choose r := by simp [hS, Finset.card_powersetCard]
  rw [Finset.sum_const, smul_eq_mul] at h3
  calc (Fintype.card X).choose r = S.card := h4.symm
    _ ≤ Fintype.card G * spec G X r := by
        rw [spec, ← hS, mul_comm]
        exact le_trans h1 (le_trans h2 h3)
