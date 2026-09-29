-- Prove2me | solution 1 for SubsetSpectrum.spec_perm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:32.836608+00:00
-- url     : https://prove2.me/submissions/f03742f5-78ca-4444-b847-2e9bec15ab28

-- Sol generated from Applications/ActionSpectrum/Basic.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Theorems.Thm_SubsetSpectrum_spec_eq_one_iff

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
    spec (Equiv.Perm X) X r = 1 := by
  rw [spec_eq_one_iff hr]
  intro s t hs ht
  have h : s.card = t.card := by rw [hs, ht]
  have hc1 : Fintype.card {x // x ∈ s} = Fintype.card {x // x ∈ t} := by
    simp [Fintype.card_coe, h]
  have hc2 : Fintype.card {x // x ∉ s} = Fintype.card {x // x ∉ t} := by
    have h1 : Fintype.card {x // x ∉ s} = Fintype.card X - s.card := by
      simp [Fintype.card_subtype_compl, Fintype.card_coe]
    have h2 : Fintype.card {x // x ∉ t} = Fintype.card X - t.card := by
      simp [Fintype.card_subtype_compl, Fintype.card_coe]
    rw [h1, h2, h]
  obtain e1 := Fintype.equivOfCardEq hc1
  obtain e2 := Fintype.equivOfCardEq hc2
  set g : Equiv.Perm X :=
    (Equiv.sumCompl (· ∈ s)).symm.trans ((e1.sumCongr e2).trans (Equiv.sumCompl (· ∈ t))) with hg
  refine ⟨g, ?_⟩
  have hsub : act g s ⊆ t := by
    intro y hy
    simp only [act, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hgx : g x = (e1 ⟨x, hx⟩ : X) := by
      simp [hg, Equiv.sumCompl_symm_apply_of_pos hx]
    simp only [Equiv.Perm.smul_def, hgx]
    exact (e1 ⟨x, hx⟩).2
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [act_card, h]
