-- Prove2me | Definitions.Def_Applications_ActionSpectrum_Basic
-- name    : Applications_ActionSpectrum_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:05:01.725605+00:00
-- url     : https://prove2.me/theorems/921962d2-2095-4156-a5eb-67c88b6e5ff4
-- title:
--   Aether Catalog definitions — Applications_ActionSpectrum_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ActionSpectrum.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ActionSpectrum/Basic.lean by skeleton subtraction
import Mathlib

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


namespace SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-! ## The induced action on finite subsets -/

/-- The induced action of `g : G` on a finite subset of `X`. -/
def act (g : G) (s : Finset X) : Finset X := s.image (fun x => g • x)

@[simp] lemma mem_act {g : G} {s : Finset X} {x : X} : x ∈ act g s ↔ g⁻¹ • x ∈ s := by
  simp only [act, mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨g⁻¹ • x, h, by simp⟩

@[simp] lemma act_one (s : Finset X) : act (1 : G) s = s := by ext x; simp

lemma act_mul (g h : G) (s : Finset X) : act (g * h) s = act g (act h s) := by
  ext x; simp [act, mul_smul]

@[simp] lemma act_card (g : G) (s : Finset X) : (act g s).card = s.card :=
  Finset.card_image_of_injective _ (MulAction.injective g)



variable (G) in
/-- The `G`-orbit of a finite subset `s ⊆ X`, as a finite set of finite subsets. -/
def orb [Fintype G] (s : Finset X) : Finset (Finset X) := univ.image (fun g : G => act g s)

variable (G X) in
/-- `spec G X r = t_r` is the number of `G`-orbits on the `r`-element subsets of `X`:
the `r`-th term of the **subset spectrum** of the action. -/
def spec [Fintype G] [Fintype X] (r : ℕ) : ℕ :=
  (((univ : Finset X).powersetCard r).image (orb G)).card

variable [Fintype G]






variable [Fintype X]

/-! ## Boundary values and support -/





/-! ## The sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` -/



/-! ## Complementation symmetry -/




/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/




end SubsetSpectrum


