-- Prove2me | solution 1 for SubsetSpectrum.card_of_mem_orb
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:20:33.405441+00:00
-- url     : https://prove2.me/submissions/d1b82391-1ea1-4cb4-95f1-3501a6058277

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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace SSWB

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G]

theorem card_of_mem_orb {s t : Finset X} (h : t ∈ orb G s) : t.card = s.card := by
  rw [orb, Finset.mem_image] at h
  obtain ⟨g, -, rfl⟩ := h
  exact act_card g s

end SSWB

theorem solution {s t : Finset X} (h : t ∈ orb G s) : t.card = s.card :=
  SSWB.card_of_mem_orb h
