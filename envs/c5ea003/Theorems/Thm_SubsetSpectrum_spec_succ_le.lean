-- Prove2me | Theorems.Thm_SubsetSpectrum_spec_succ_le
-- name    : SubsetSpectrum.spec_succ_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:32.796603+00:00
-- url     : https://prove2.me/theorems/0d83eaaf-fb03-4d50-b0da-19e277b25339
-- title:
--   Extension bound.
-- statement:
--   **Extension bound.**  Every orbit of `(r+1)`-element subsets arises by adjoining one of
--   the `n - r` outside points to the chosen representative of an orbit of `r`-element subsets.
--   Consequently `t_{r+1} ≤ (n - r)·t_r`.
--
--   ```lean
--   theorem SubsetSpectrum.spec_succ_le(r : ℕ) :
--       spec G X (r + 1) ≤ (Fintype.card X - r) * spec G X r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ActionSpectrum/Shadow.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ActionSpectrum/Shadow.lean#L48

-- Thm stub generated from Applications/ActionSpectrum/Shadow.lean
import Mathlib
import Definitions.Def_Applications_ActionSpectrum_Basic
import Definitions.Def_Applications_ActionSpectrum_Shadow

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

theorem SubsetSpectrum.spec_succ_le(r : ℕ) :
    spec G X (r + 1) ≤ (Fintype.card X - r) * spec G X r := by sorry
