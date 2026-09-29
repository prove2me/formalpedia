-- Prove2me | solution 1 for SubsetSpectrum.not_logConcave_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:28:05.602069+00:00
-- url     : https://prove2.me/submissions/909b64f5-6b81-4c9d-b3c6-2b96a3596d16

-- Sol generated from Applications/ActionSpectrum/LogConcavity.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Definitions.Def_Applications_ActionSpectrum_LogConcavity
import Theorems.Thm_SubsetSpectrum_choose_le_card_mul_spec
import Theorems.Thm_SubsetSpectrum_logConcave_iff_setTransitive

/-!
# Log-concavity of the subset spectrum of a finite action

The research target of this file is the claim

> for every finite action the spectrum is log-concave: `t_r² ≥ t_{r-1}·t_{r+1}` for `1 ≤ r < |X|`.

**The claim is false.**  The cyclic group of order `4` acting on `4` points has spectrum
`(1, 1, 2, 1, 1)`, and `t_1² = 1 < 2 = t_0·t_2` (`SubsetSpectrum.C4.not_logConcaveSpectrum`,
`SubsetSpectrum.not_forall_logConcaveSpectrum`).

What we prove instead is a complete structural explanation of *when* the claim holds,
plus a quantitative repair that is valid for every finite action:

* `SubsetSpectrum.logConcave_of_trivial_action` — for the trivial action the spectrum is the
  binomial row and log-concavity **does** hold (so the statement is not vacuous);
* `SubsetSpectrum.spec_mul_spec_le_card_sq_mul_spec_sq` — the **guarded universal version**
  `t_{r-1}·t_{r+1} ≤ |G|²·t_r²`, valid for *every* finite action;
* `SubsetSpectrum.spec_eq_one_of_logConcave` — a **collapse/propagation theorem**: once two
  consecutive spectrum values equal `1`, log-concavity forces *all* later values to be `1`;
* `SubsetSpectrum.logConcave_iff_setTransitive` — hence for a *transitive* action,
  log-concavity of the spectrum is **equivalent** to set-transitivity (`r`-homogeneity for
  every `r`), a drastic rigidity statement: the conjecture holds only for the handful of
  set-transitive permutation groups;
* `SubsetSpectrum.choose_le_card_of_transitive_logConcave` — the resulting numerical
  obstruction `C(n,r) ≤ |G|` for all `r`, so a log-concave transitive action needs a group
  of exponential size;
* `SubsetSpectrum.not_logConcave_of_regular` — an **infinite family of counterexamples**:
  every regular action on `n ≥ 4` points (a group acting on itself by translation) fails
  log-concavity;
* `SubsetSpectrum.logConcave_perm` — the symmetric group is such an action, so the class of
  log-concave transitive actions is nonempty.

A group-free sharpening of the guarded bound, `t_{r-1}·t_{r+1} ≤ r(n-r)·t_r²`, is proved by a
shadow argument in `Applications.ActionSpectrum.Shadow`.

## Lab notes (computed with the executable model `SubsetSpectrum.spec`)

Spectra of the cyclic group `C_n` acting on `n` points (binary necklaces by weight):

```
n = 3 : 1 1 1 1
n = 4 : 1 1 2 1 1
n = 5 : 1 1 2 2 1 1
n = 6 : 1 1 3 4 3 1 1
n = 7 : 1 1 3 5 5 3 1 1
n = 8 : 1 1 4 7 10 7 4 1 1
```

Every one of these fails log-concavity at `r = 1` (and, by the symmetry `t_r = t_{n-r}`,
at `r = n-1`) as soon as `n ≥ 4`.  The trivial group on `4` points gives `1 4 6 4 1`
(log-concave), `S_4` and `A_4` on `4` points give `1 1 1 1 1` (log-concave).
-/

open Finset

open SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]

/-! ## The property under investigation -/



/-! ## A genuine positive instance: the trivial action -/



/-! ## The guarded universal version, valid for every finite action -/


/-! ## The collapse theorem: log-concavity forces the spectrum to be constantly `1` -/



/-- A transitive log-concave action forces the acting group to be enormous:
`C(n,r) ≤ |G|` for every `r ≤ n` (so `|G| ≥ C(n, ⌊n/2⌋)`). -/
theorem choose_le_card_of_transitive_logConcave (htrans : spec G X 1 = 1)
    (hlc : LogConcaveSpectrum G X) (r : ℕ) (hr : r ≤ Fintype.card X) :
    (Fintype.card X).choose r ≤ Fintype.card G := by
  have h1 : spec G X r = 1 := (logConcave_iff_setTransitive htrans).1 hlc r hr
  have := choose_le_card_mul_spec (G := G) (X := X) r
  rwa [h1, mul_one] at this

/-- **Cardinality obstruction.**  A transitive action of a group that is smaller than some
binomial coefficient `C(n,r)` cannot have a log-concave spectrum. -/
theorem not_logConcave_of_card_lt_choose (htrans : spec G X 1 = 1) {r : ℕ}
    (hr : r ≤ Fintype.card X) (hcard : Fintype.card G < (Fintype.card X).choose r) :
    ¬ LogConcaveSpectrum G X := by
  intro hlc
  exact absurd (choose_le_card_of_transitive_logConcave htrans hlc r hr) (by omega)




/-! ## Counterexamples: the regular actions of cyclic groups -/





open SubsetSpectrum
open Cyc

variable (n : ℕ) [NeZero n]




open C4








open SubsetSpectrum in
theorem solution(htrans : spec G X 1 = 1)
    (hreg : Fintype.card G = Fintype.card X) (hn : 4 ≤ Fintype.card X) :
    ¬ LogConcaveSpectrum G X := by
  have key : ∀ n : ℕ, 4 ≤ n → n < n.choose 2 := by
    intro n hn
    rw [Nat.choose_two_right]
    have h : (n + 1) * 2 ≤ n * (n - 1) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hm : m + 4 - 1 = m + 3 := by omega
      rw [hm]
      nlinarith
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 h
    omega
  exact not_logConcave_of_card_lt_choose htrans (r := 2) (by omega)
    (by rw [hreg]; exact key _ hn)
