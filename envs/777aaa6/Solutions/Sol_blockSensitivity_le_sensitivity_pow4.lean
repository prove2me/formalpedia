-- Prove2me | solution 1 for blockSensitivity_le_sensitivity_pow4
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-04-24T03:48:27.649949+00:00
-- url     : https://prove2.me/submissions/c113cfd6-f8ac-435e-b6be-89f55275a215
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_blockSensitivity_le_sensitivity_pow4
import Theorems.Thm_sensitivity_sq_ge_polyDegree
import Theorems.Thm_tal_block_sensitivity_bound
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_blockSensitivity
import Definitions.Def_polyDegree

/-!
# Sketch — Huang 2019, Theorem 1.5

Chain (Huang 2019 §1):
* Tal 2013 (`tal_block_sensitivity_bound`):  `bs(f) ≤ 2·deg(f)²`.
* Huang Thm 1.4 (`sensitivity_sq_ge_polyDegree`):  `deg(f) ≤ s(f)²`.
* Substitute and simplify:  `bs(f) ≤ 2·(s(f)²)² = 2·s(f)⁴`.
-/

theorem solution {n : ℕ} (f : BoolFunc n) :
    blockSensitivity f ≤ 2 * (sensitivity f) ^ 4 := by
  have h_tal : blockSensitivity f ≤ 2 * polyDegree f ^ 2 :=
    tal_block_sensitivity_bound f
  have h_deg : polyDegree f ≤ (sensitivity f) ^ 2 :=
    sensitivity_sq_ge_polyDegree f
  have h_deg_sq : polyDegree f ^ 2 ≤ ((sensitivity f) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left h_deg 2
  have h_pow_eq : ((sensitivity f) ^ 2) ^ 2 = (sensitivity f) ^ 4 := by ring
  calc blockSensitivity f
      ≤ 2 * polyDegree f ^ 2 := h_tal
    _ ≤ 2 * ((sensitivity f) ^ 2) ^ 2 := Nat.mul_le_mul_left 2 h_deg_sq
    _ = 2 * (sensitivity f) ^ 4 := by rw [h_pow_eq]
