-- Prove2me | Theorems.Thm_polynomial_eval_norm_tendsto_cobounded
-- name    : polynomial_eval_norm_tendsto_cobounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:35:14.707427+00:00
-- url     : https://prove2.me/theorems/508aa74d-a424-4ed0-a4eb-292f1a9bef96
-- statement:
--   **Growth at infinity.** For a complex polynomial $f$ of positive degree, $\|f(z)\| \to \infty$ as $z$ leaves every bounded set (the `cobounded` filter on $\mathbb{C}$).
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Analysis.Complex.Polynomial.Basic
open Polynomial Filter

theorem polynomial_eval_norm_tendsto_cobounded {f : ℂ[X]} (hf : 0 < degree f) : Tendsto (fun z : ℂ => ‖f.eval z‖) (Bornology.cobounded ℂ) atTop := by sorry
