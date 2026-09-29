-- Prove2me | solution 1 for Nat.choose_mul_choose_le_choose_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:46:10.972931+00:00
-- url     : https://prove2.me/submissions/4be2123d-eff4-467c-93b4-21943b9da1a6

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










variable [Fintype G]






variable [Fintype X]

/-! ## Boundary values and support -/





/-! ## The sandwich `C(n,r)/|G| ≤ t_r ≤ C(n,r)` -/



/-! ## Complementation symmetry -/




/-! ## Two extreme actions -/


/-! ## `t_r = 1` and `r`-homogeneity -/





theorem solution(n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ n.choose (k + 1) ^ 2 := by
  rcases Nat.lt_or_ge (k + 1) n with hn | hn
  · set a := n.choose k
    set b := n.choose (k + 1)
    set c := n.choose (k + 2)
    have h1 : b * (k + 1) = a * (n - k) := Nat.choose_succ_right_eq n k
    have h2 : c * (k + 2) = b * (n - (k + 1)) := Nat.choose_succ_right_eq n (k + 1)
    have hnk : n - k = (n - (k + 1)) + 1 := by omega
    set m := n - (k + 1) with hm
    have key : a * c * ((k + 1) * (k + 2)) ≤ b ^ 2 * ((k + 1) * (k + 2)) := by
      have e1 : a * c * ((k + 1) * (k + 2)) = (a * (k + 1)) * (c * (k + 2)) := by ring
      have e2 : b ^ 2 * ((k + 1) * (k + 2)) = (b * (k + 1)) * (b * (k + 2)) := by ring
      rw [e1, e2, h1, h2, hnk]
      have hstep : (k + 1) * m ≤ (m + 1) * (k + 2) := by nlinarith
      calc a * (k + 1) * (b * m) = (a * b) * ((k + 1) * m) := by ring
        _ ≤ (a * b) * ((m + 1) * (k + 2)) := Nat.mul_le_mul_left _ hstep
        _ = a * (m + 1) * (b * (k + 2)) := by ring
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  · have : n.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
