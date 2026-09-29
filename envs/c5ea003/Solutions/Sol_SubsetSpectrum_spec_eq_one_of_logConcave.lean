-- Prove2me | solution 1 for SubsetSpectrum.spec_eq_one_of_logConcave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:23:22.289283+00:00
-- url     : https://prove2.me/submissions/8aedf850-a1d3-4389-9ec7-1f0debb7b4ac

-- Sol generated from Applications/ActionSpectrum/LogConcavity.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Definitions.Def_Applications_ActionSpectrum_LogConcavity
import Theorems.Thm_SubsetSpectrum_spec_pos

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


/-- Reindexed form of log-concavity, free of truncated subtraction. -/
theorem logConcaveSpectrum_iff :
    LogConcaveSpectrum G X ↔
      ∀ k : ℕ, k + 2 ≤ Fintype.card X →
        spec G X k * spec G X (k + 2) ≤ spec G X (k + 1) ^ 2 := by
  constructor
  · intro h k hk
    have := h (k + 1) (by omega) (by omega)
    simpa using this
  · intro h r h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simpa using h k (by omega)

/-! ## A genuine positive instance: the trivial action -/



/-! ## The guarded universal version, valid for every finite action -/


/-! ## The collapse theorem: log-concavity forces the spectrum to be constantly `1` -/








/-! ## Counterexamples: the regular actions of cyclic groups -/





open SubsetSpectrum
open Cyc

variable (n : ℕ) [NeZero n]




open C4








open SubsetSpectrum in
theorem solution{m : ℕ} (hm : spec G X m = 1) (hm1 : spec G X (m + 1) = 1)
    (hlc : LogConcaveSpectrum G X) :
    ∀ r : ℕ, m ≤ r → r ≤ Fintype.card X → spec G X r = 1 := by
  rw [logConcaveSpectrum_iff] at hlc
  -- two-step induction: the pair `(t_{m+j}, t_{m+j+1})` stays `(1,1)`
  have key : ∀ j : ℕ, m + j ≤ Fintype.card X →
      spec G X (m + j) = 1 ∧ (m + j + 1 ≤ Fintype.card X → spec G X (m + j + 1) = 1) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simpa using hm, fun _ => by simpa using hm1⟩
    | succ j ih =>
        intro hj
        have hj' : m + j ≤ Fintype.card X := by omega
        obtain ⟨h0, h1⟩ := ih hj'
        have h1' : spec G X (m + j + 1) = 1 := h1 (by omega)
        have e1 : m + (j + 1) = m + j + 1 := by omega
        rw [e1, show m + j + 1 + 1 = m + j + 2 from by omega]
        refine ⟨h1', ?_⟩
        intro _
        have hlc' := hlc (m + j) (by omega)
        rw [h0, h1'] at hlc'
        have hpos : 0 < spec G X (m + j + 2) := spec_pos (by omega)
        have hle : spec G X (m + j + 2) ≤ 1 := by
          calc spec G X (m + j + 2) = 1 * spec G X (m + j + 2) := (one_mul _).symm
            _ ≤ 1 ^ 2 := hlc'
            _ = 1 := one_pow 2
        omega
  intro r hmr hrn
  obtain ⟨j, rfl⟩ : ∃ j, r = m + j := ⟨r - m, by omega⟩
  exact (key j hrn).1
