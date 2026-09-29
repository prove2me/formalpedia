-- Prove2me | Theorems.Thm_liouville_const_of_tendsto_cocompact
-- name    : liouville_const_of_tendsto_cocompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:20:11.680182+00:00
-- url     : https://prove2.me/theorems/7643da1a-52e6-4f72-87e6-51e1370413f7
-- statement:
--   **Liouville (limit-at-infinity form).** An entire function $g : \mathbb{C} \to \mathbb{C}$ that tends to a finite limit $c$ along the `cocompact` filter is constant equal to $c$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Complex.Liouville
open Filter Topology

theorem liouville_const_of_tendsto_cocompact {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} (hgc : Tendsto g (cocompact ℂ) (𝓝 c)) (z : ℂ) : g z = c := by sorry
