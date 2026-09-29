-- Prove2me | solution 1 for sensitivity_conjecture
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-04-24T03:49:01.099824+00:00
-- url     : https://prove2.me/submissions/c64877e3-b0c8-434f-bc1e-e3b0ebf8cba4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_sensitivity_conjecture
import Theorems.Thm_blockSensitivity_le_sensitivity_pow4
import Definitions.Def_BoolFunc
import Definitions.Def_sensitivity
import Definitions.Def_blockSensitivity

/-!
# Sketch — Sensitivity Conjecture

Witness the existential with `C = 2, k = 4`, discharging the body by
Huang 2019 Thm 1.5 (`blockSensitivity_le_sensitivity_pow4`).
-/

theorem solution :
    ∃ C k : ℕ, ∀ (n : ℕ) (f : BoolFunc n),
      blockSensitivity f ≤ C * (sensitivity f) ^ k :=
  ⟨2, 4, fun _ f => blockSensitivity_le_sensitivity_pow4 f⟩
