-- Prove2me | Theorems.Thm_poly_norm_has_global_min
-- name    : poly_norm_has_global_min
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-22T14:07:54.509632+00:00
-- url     : https://prove2.me/theorems/bb4daa6a-9913-49a7-9695-a2965541e0e1
-- statement:
--   For a complex polynomial $f$, the modulus $\|f(z)\|$ attains a global minimum over $\mathbb{C}$: there is a point $c$ with $\|f(c)\| \le \|f(z)\|$ for all $z$.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic
open Polynomial

theorem poly_norm_has_global_min (f : ℂ[X]) : ∃ c : ℂ, ∀ z : ℂ, ‖f.eval c‖ ≤ ‖f.eval z‖ := by sorry
