-- Prove2me | solution 1 for SubsetSpectrum.spec_compl
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:28:06.683617+00:00
-- url     : https://prove2.me/submissions/f42c0b45-7997-4466-9278-c658ad8f49e0

-- Sol generated from Applications/ActionSpectrum/Basic.lean
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






lemma act_compl [Fintype X] (g : G) (s : Finset X) : act g sᶜ = (act g s)ᶜ := by ext x; simp




variable [Fintype G]






variable [Fintype X]

/-! ## Boundary values and support -/





/-! ## The sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` -/



/-! ## Complementation symmetry -/

lemma orb_compl (s : Finset X) : (orb G s).image (fun u => uᶜ) = orb G sᶜ := by
  simp only [orb, Finset.image_image]
  exact Finset.image_congr (fun g _ => by simp [Function.comp, act_compl])

lemma powersetCard_compl {r : ℕ} (hr : r ≤ Fintype.card X) :
    ((univ : Finset X).powersetCard r).image (fun s => sᶜ)
      = (univ : Finset X).powersetCard (Fintype.card X - r) := by
  ext s
  simp only [mem_image, mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨u, hu, rfl⟩; rw [card_compl, hu]
  · intro hs; exact ⟨sᶜ, by rw [card_compl, hs]; omega, compl_compl s⟩


/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/





open SubsetSpectrum in
theorem solution{r : ℕ} (hr : r ≤ Fintype.card X) :
    spec G X (Fintype.card X - r) = spec G X r := by
  have hinj :
      Function.Injective (fun O : Finset (Finset X) => O.image (fun u : Finset X => uᶜ)) := by
    intro O P hOP
    have := congrArg (fun Q : Finset (Finset X) => Q.image (fun u : Finset X => uᶜ)) hOP
    simpa [Finset.image_image, Function.comp] using this
  have key : ((univ : Finset X).powersetCard (Fintype.card X - r)).image (orb G)
      = (((univ : Finset X).powersetCard r).image (orb G)).image
          (fun O : Finset (Finset X) => O.image (fun u : Finset X => uᶜ)) := by
    rw [Finset.image_image, ← powersetCard_compl hr, Finset.image_image]
    exact Finset.image_congr (fun s _ => (orb_compl s).symm)
  rw [spec, spec, key, Finset.card_image_of_injective _ hinj]
