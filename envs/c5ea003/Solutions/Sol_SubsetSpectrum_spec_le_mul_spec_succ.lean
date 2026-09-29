-- Prove2me | solution 1 for SubsetSpectrum.spec_le_mul_spec_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:31.380099+00:00
-- url     : https://prove2.me/submissions/f2691901-fa80-4f57-b4ef-00043a0bf66f

-- Sol generated from Applications/ActionSpectrum/Shadow.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Definitions.Def_Applications_ActionSpectrum_Shadow
import Theorems.Thm_SubsetSpectrum_spec_compl
import Theorems.Thm_SubsetSpectrum_spec_succ_le

/-!
# Shadow inequalities for the subset spectrum, and a group-free log-concavity guard

The guarded log-concavity bound of `Applications.ActionSpectrum.LogConcavity`
(`t_{r-1}·t_{r+1} ≤ |G|²·t_r²`) degrades badly for large groups.  Here we prove a bound
which does **not** mention `|G|` at all, by a shadow (deletion/extension) argument on
orbits:

* `SubsetSpectrum.spec_succ_le` : `t_{r+1} ≤ (n - r) · t_r`;
* `SubsetSpectrum.spec_le_mul_spec_succ` : `t_r ≤ (r + 1) · t_{r+1}` (by complementation);
* `SubsetSpectrum.spec_mul_spec_le_shadow_bound` : `t_{r-1} · t_{r+1} ≤ r·(n-r) · t_r²`.

The last inequality is the *sharp shape* of the failed conjecture: the spectrum of any
finite action is log-concave up to the factor `r(n-r)`, which is exactly the failure ratio
of the binomial recursion at the boundary.  For the counterexample `C₄` on `4` points at
`r = 1` it reads `t_0·t_2 = 2 ≤ 1·3·1 = 3`.

The engine is:

> every orbit of `(r+1)`-sets is obtained from a *fixed representative* `s` of some orbit of
> `r`-sets by adding one of the `n - r` points outside `s`.
-/

open Finset

open SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]









open SubsetSpectrum in
theorem solution(r : ℕ) (hr : r + 1 ≤ Fintype.card X) :
    spec G X r ≤ (r + 1) * spec G X (r + 1) := by
  set n := Fintype.card X with hn
  have h1 : spec G X r = spec G X (n - r) := (spec_compl (G := G) (X := X) (by omega)).symm
  have h2 : spec G X (r + 1) = spec G X (n - (r + 1)) :=
    (spec_compl (G := G) (X := X) (by omega)).symm
  have hkey := spec_succ_le (G := G) (X := X) (n - (r + 1))
  have he : n - (r + 1) + 1 = n - r := by omega
  rw [he] at hkey
  have hcoef : n - (n - (r + 1)) = r + 1 := by omega
  rw [hcoef] at hkey
  rw [h1, h2]
  exact hkey
