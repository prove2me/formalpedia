-- Prove2me | Definitions.Def_Applications_ActionSpectrum_Shadow
-- name    : Applications_ActionSpectrum_Shadow
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:10:23.106216+00:00
-- url     : https://prove2.me/theorems/40c07e3f-50de-498d-a1b0-61fd5e17be3c
-- title:
--   Aether Catalog definitions — Applications_ActionSpectrum_Shadow
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ActionSpectrum.Shadow`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ActionSpectrum/Shadow.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic

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

namespace SubsetSpectrum

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X] [Fintype G] [Fintype X]



/-- A choice of representative of a nonempty finite family of subsets. -/
noncomputable def rep (O : Finset (Finset X)) : Finset X :=
  if h : O.Nonempty then h.choose else ∅





end SubsetSpectrum


