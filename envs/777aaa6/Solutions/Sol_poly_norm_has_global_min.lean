-- Prove2me | solution 1 for poly_norm_has_global_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-22T14:09:34.510096+00:00
-- url     : https://prove2.me/submissions/ab3b99a6-49cf-4fd3-aedd-fffbf050ffc2

import Theorems.Thm_poly_norm_has_global_min
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic

/-!
# Solution — `poly_norm_has_global_min` (Child 1)

Direct proof: `Polynomial.exists_forall_norm_le` says that over a proper space
(`ℂ` is one), `‖p.eval‖` attains a global minimum. That is exactly the claim.

`theorem solution` matches the target type of `Thm_poly_norm_has_global_min`;
submit with `proof_type=prove`.
-/

open Polynomial

theorem solution (f : ℂ[X]) :
    ∃ c : ℂ, ∀ z : ℂ, ‖f.eval c‖ ≤ ‖f.eval z‖ :=
  f.exists_forall_norm_le
