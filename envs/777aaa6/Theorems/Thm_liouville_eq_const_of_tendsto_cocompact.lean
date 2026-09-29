-- Prove2me | Theorems.Thm_liouville_eq_const_of_tendsto_cocompact
-- name    : liouville_eq_const_of_tendsto_cocompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:35:20.446311+00:00
-- url     : https://prove2.me/theorems/90e84879-2915-46c5-b85a-cf66a265eb3b
-- statement:
--   **Liouville (limit-at-infinity form).** An entire function $g:\mathbb{C}\to\mathbb{C}$ that tends to a finite limit $c$ along the `cocompact` filter is constant equal to $c$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Complex.Polynomial.Basic
open Filter Topology

theorem liouville_eq_const_of_tendsto_cocompact {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} (hgc : Tendsto g (cocompact ℂ) (𝓝 c)) (z : ℂ) : g z = c := by sorry
