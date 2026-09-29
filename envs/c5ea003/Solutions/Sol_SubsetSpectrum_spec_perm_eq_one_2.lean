-- Prove2me | solution 2 for SubsetSpectrum.spec_perm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:14:45.96277+00:00
-- url     : https://prove2.me/submissions/57ea7a49-b4b4-4e8f-bc0c-9e5543132a5d

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



/-! ## Complementation symmetry -/




/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace SSWB

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]

theorem mem_orb_self (s : Finset X) : s ∈ orb G s := by
  rw [orb, Finset.mem_image]
  exact ⟨1, Finset.mem_univ 1, act_one s⟩

theorem orb_eq_of_mem {s t : Finset X} (h : t ∈ orb G s) : orb G t = orb G s := by
  rw [orb, Finset.mem_image] at h
  obtain ⟨g, -, rfl⟩ := h
  ext r
  simp only [orb, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, act_mul h g s⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h * g⁻¹, by rw [← act_mul, inv_mul_cancel_right]⟩

theorem spec_eq_one_iff {r : ℕ} (hr : r ≤ Fintype.card X) :
    spec G X r = 1 ↔ ∀ s t : Finset X, s.card = r → t.card = r → ∃ g : G, act g s = t := by
  classical
  constructor
  · intro h s t hs ht
    have h' : (((univ : Finset X).powersetCard r).image (orb G)).card = 1 := h
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h'
    have hs' : orb G s ∈ ((univ : Finset X).powersetCard r).image (orb G) :=
      Finset.mem_image_of_mem _ (Finset.mem_powersetCard.2 ⟨Finset.subset_univ s, hs⟩)
    have ht' : orb G t ∈ ((univ : Finset X).powersetCard r).image (orb G) :=
      Finset.mem_image_of_mem _ (Finset.mem_powersetCard.2 ⟨Finset.subset_univ t, ht⟩)
    rw [ha, Finset.mem_singleton] at hs' ht'
    have hmem : t ∈ orb G s := by rw [hs', ← ht']; exact mem_orb_self t
    rw [orb, Finset.mem_image] at hmem
    obtain ⟨g, -, hg⟩ := hmem
    exact ⟨g, hg⟩
  · intro h
    obtain ⟨s₀, hs₀⟩ := (Finset.powersetCard_nonempty (s := (univ : Finset X)) (n := r)).2
      (by rwa [Finset.card_univ])
    have hs₀card : s₀.card = r := (Finset.mem_powersetCard.1 hs₀).2
    show (((univ : Finset X).powersetCard r).image (orb G)).card = 1
    refine Finset.card_eq_one.2 ⟨orb G s₀, ?_⟩
    ext b
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨g, hg⟩ := h s₀ s hs₀card (Finset.mem_powersetCard.1 hs).2
      refine orb_eq_of_mem ?_
      rw [orb, Finset.mem_image]
      exact ⟨g, Finset.mem_univ g, hg⟩
    · rintro rfl
      exact ⟨s₀, hs₀, rfl⟩

theorem spec_perm_eq_one {r : ℕ} (hr : r ≤ Fintype.card X) :
    spec (Equiv.Perm X) X r = 1 := by
  classical
  rw [spec_eq_one_iff hr]
  intro s t hs ht
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq s t (by rw [hs, ht])
  refine ⟨σ, ?_⟩
  rw [act, ← hσ, Finset.map_eq_image]
  rfl

end SSWB

theorem solution {r : ℕ} (hr : r ≤ Fintype.card X) :
    spec (Equiv.Perm X) X r = 1 :=
  SSWB.spec_perm_eq_one hr
