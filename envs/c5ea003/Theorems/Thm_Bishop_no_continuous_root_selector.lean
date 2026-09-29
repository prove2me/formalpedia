-- Prove2me | Theorems.Thm_Bishop_no_continuous_root_selector
-- name    : Bishop.no_continuous_root_selector
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:48.100922+00:00
-- url     : https://prove2.me/theorems/750d11d5-aafc-420e-b2d1-91b143b3f379
-- title:
--   Brouwerian counterexample to the exact intermediate value theorem.
-- statement:
--   **Brouwerian counterexample to the exact intermediate value theorem.**
--
--   There is no continuous choice of a root for the family `shelf t`, `t ∈ [-1,1]`,
--   even though each member is `1`-Lipschitz and changes sign on `[0,3]`.  Hence no
--   constructive (computable) procedure can produce exact roots from these data.
--
--   ```lean
--   theorem Bishop.no_continuous_root_selector:
--       ¬ ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-1 : ℝ) 1) ∧
--         ∀ t ∈ Icc (-1 : ℝ) 1, shelf t (r t) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean#L97

-- Thm stub generated from Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BrouwerianCounterexamples
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
/-
# A Brouwerian counterexample: the exact IVT has no continuous solution operator

This file makes precise the sense in which the *exact* intermediate value theorem
fails constructively, while the approximate one (proved in
`Logic/ConstructiveAnalysis/ConstructiveIVT.lean`) holds.

We use Bishop's standard family of "shelf" functions

  `shelf t x = min (x - 1) (max t (x - 2))`,   `t ∈ [-1,1]`, `x ∈ [0,3]`.

Each `shelf t` is `1`-Lipschitz (so it has the explicit modulus of uniform
continuity `ω = id`), and satisfies `shelf t 0 ≤ 0 ≤ shelf t 3`, so the approximate
IVT applies to the whole family uniformly (`shelf_approx_root`).  Nevertheless:

* `shelf_root_of_mem_Ioo` : if `1 < x < 2` and `shelf t x = 0` then `t = 0`;
* `no_continuous_root_selector` : there is **no continuous** map `t ↦ r t` on
  `[-1,1]` with `shelf t (r t) = 0`.

Since every constructively (in particular, computably) defined map `ℝ → ℝ` is
continuous, this shows that no constructive proof of the exact IVT can exist: the
root cannot be obtained continuously — let alone computably — from the data.
The hypothesis that rescues the exact IVT in `constructive_ivt` is a positive lower
slope bound; `shelf_zero_slope_bound_nonpos` shows that this is precisely what the
family violates at `t = 0`, where `shelf 0` is constant on `[1,2]`.
-/


open Bishop

open Set

theorem Bishop.no_continuous_root_selector:
    ¬ ∃ r : ℝ → ℝ, ContinuousOn r (Icc (-1 : ℝ) 1) ∧
      ∀ t ∈ Icc (-1 : ℝ) 1, shelf t (r t) = 0 := by sorry
