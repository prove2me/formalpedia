-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_BrouwerianCounterexamples
-- name    : Logic_ConstructiveAnalysis_BrouwerianCounterexamples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:50:42.545719+00:00
-- url     : https://prove2.me/theorems/dd59bd7e-fa9b-4f2b-ac01-920f1cf4f9aa
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_BrouwerianCounterexamples
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.BrouwerianCounterexamples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean by skeleton subtraction
import Mathlib
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


namespace Bishop

open Set

/-- Bishop's "shelf" family: a `1`-Lipschitz family of functions on `[0,3]` whose
root jumps from `1` to `2` as the parameter `t` crosses `0`. -/
noncomputable def shelf (t x : ℝ) : ℝ := min (x - 1) (max t (x - 2))












end Bishop


