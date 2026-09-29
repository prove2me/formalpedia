-- Prove2me | Theorems.Thm_SubsetSpectrum_spec_le_mul_spec_succ
-- name    : SubsetSpectrum.spec_le_mul_spec_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:04:34.695385+00:00
-- url     : https://prove2.me/theorems/fb1bcb79-7e8f-4fe2-83d6-f2332eb21ac0
-- title:
--   Deletion bound (dual of `spec_succ_le`, obtained by complementation):
-- statement:
--   **Deletion bound** (dual of `spec_succ_le`, obtained by complementation):
--   `t_r ≤ (r + 1)·t_{r+1}`.
--
--   ```lean
--   theorem SubsetSpectrum.spec_le_mul_spec_succ(r : ℕ) (hr : r + 1 ≤ Fintype.card X) :
--       spec G X r ≤ (r + 1) * spec G X (r + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ActionSpectrum/Shadow.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ActionSpectrum/Shadow.lean#L111

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

theorem SubsetSpectrum.spec_le_mul_spec_succ(r : ℕ) (hr : r + 1 ≤ Fintype.card X) :
    spec G X r ≤ (r + 1) * spec G X (r + 1) := by sorry
