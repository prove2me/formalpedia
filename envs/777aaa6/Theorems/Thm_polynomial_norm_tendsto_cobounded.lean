-- Prove2me | Theorems.Thm_polynomial_norm_tendsto_cobounded
-- name    : polynomial_norm_tendsto_cobounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:20:03.850481+00:00
-- url     : https://prove2.me/theorems/a1d5ac3d-a4e2-428c-9c43-40b68ff38e1f
-- statement:
--   **Growth at infinity.** For a complex polynomial $f$ of positive degree, $\|f(z)\| \to \infty$ as $z$ leaves every bounded set (the `cobounded` filter on $\mathbb{C}$).
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Liouville
open Polynomial Filter Bornology

theorem polynomial_norm_tendsto_cobounded {f : ℂ[X]} (hf : 0 < degree f) : Tendsto (fun z : ℂ => ‖f.eval z‖) (cobounded ℂ) atTop := by sorry
