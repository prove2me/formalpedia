-- Prove2me | solution 1 for SubsetSpectrum.spec_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:30:56.867051+00:00
-- url     : https://prove2.me/submissions/68feaba4-1579-4110-b334-83a1f780a5b3

-- Sol generated from Applications/ActionSpectrum/Basic.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Theorems.Thm_SubsetSpectrum_mem_orb_self
import Theorems.Thm_SubsetSpectrum_orb_eq_of_mem

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



/-! ## Complementation symmetry -/




/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/





open SubsetSpectrum in
theorem solution{r : ℕ} (hr : r ≤ Fintype.card X) :
    spec G X r = 1 ↔ ∀ s t : Finset X, s.card = r → t.card = r → ∃ g : G, act g s = t := by
  constructor
  · intro h s t hs ht
    obtain ⟨O, hO⟩ := Finset.card_eq_one.1 h
    have hs' : s ∈ (univ : Finset X).powersetCard r := mem_powersetCard.2 ⟨subset_univ _, hs⟩
    have ht' : t ∈ (univ : Finset X).powersetCard r := mem_powersetCard.2 ⟨subset_univ _, ht⟩
    have h1 : orb G s = O := by
      have := Finset.mem_image_of_mem (orb G) hs'
      rw [hO, Finset.mem_singleton] at this
      exact this
    have h2 : orb G t = O := by
      have := Finset.mem_image_of_mem (orb G) ht'
      rw [hO, Finset.mem_singleton] at this
      exact this
    have hmem : t ∈ orb G s := by rw [h1, ← h2]; exact mem_orb_self _
    simp only [orb, mem_image, mem_univ, true_and] at hmem
    exact hmem
  · intro h
    obtain ⟨s₀, hs₀⟩ := Finset.powersetCard_nonempty.2 (le_trans hr (le_of_eq Finset.card_univ.symm))
    refine Finset.card_eq_one.2 ⟨orb G s₀, Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_image_of_mem _ hs₀, ?_⟩⟩
    rintro O hO
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hO
    obtain ⟨g, hg⟩ := h s₀ s (mem_powersetCard.1 hs₀).2 (mem_powersetCard.1 hs).2
    exact orb_eq_of_mem (by simp only [orb, mem_image, mem_univ, true_and]; exact ⟨g, hg⟩)
