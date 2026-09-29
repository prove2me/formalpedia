-- Prove2me | Theorems.Thm_sensitivity_sq_ge_polyDegree
-- name    : sensitivity_sq_ge_polyDegree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-04-24T03:38:24.006816+00:00
-- url     : https://prove2.me/theorems/f8cd7ff4-f9d8-4417-829e-22866a73f9b7
-- statement:
--   Huang 2019 Theorem 1.4: for every Boolean function f, deg(f) <= s(f)^2, i.e. s(f) >= sqrt(deg f).
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_polyDegree

/-!
# Huang 2019, Theorem 1.4

The sensitivity/degree lower bound obtained by combining Huang's
Thm 1.1 (induced-subgraph max-degree bound on the signed hypercube)
with Gotsman–Linial 1992: for every Boolean function,
`deg(f) ≤ s(f)²`, i.e. `s(f) ≥ √(deg f)`.
-/

/-- **Huang 2019, Thm 1.4.**  For every Boolean function
    `f : {0,1}ⁿ → {0,1}`,
    the polynomial degree is at most the sensitivity squared:
    `deg(f) ≤ s(f)²`. -/

theorem sensitivity_sq_ge_polyDegree
    {n : ℕ} (f : BoolFunc n) :
    polyDegree f ≤ (sensitivity f) ^ 2 := by sorry
