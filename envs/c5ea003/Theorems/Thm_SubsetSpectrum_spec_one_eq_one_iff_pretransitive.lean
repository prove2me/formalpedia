-- Prove2me | Theorems.Thm_SubsetSpectrum_spec_one_eq_one_iff_pretransitive
-- name    : SubsetSpectrum.spec_one_eq_one_iff_pretransitive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:45.403972+00:00
-- url     : https://prove2.me/theorems/9d0e48ba-b222-417a-aa00-e5252fcbe967
-- title:
--   `t_1 = 1` is exactly transitivity of the action (for nonempty `X`).
-- statement:
--   **`t_1 = 1` is exactly transitivity** of the action (for nonempty `X`).
--
--   ```lean
--   theorem SubsetSpectrum.spec_one_eq_one_iff_pretransitive[Nonempty X] :
--       spec G X 1 = 1 ↔ ∀ x y : X, ∃ g : G, g • x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ActionSpectrum/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ActionSpectrum/Basic.lean#L257

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

theorem SubsetSpectrum.spec_one_eq_one_iff_pretransitive[Nonempty X] :
    spec G X 1 = 1 ↔ ∀ x y : X, ∃ g : G, g • x = y := by sorry
