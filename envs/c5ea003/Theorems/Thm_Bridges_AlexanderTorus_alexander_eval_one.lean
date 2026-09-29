-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_eval_one
-- name    : Bridges.AlexanderTorus.alexander_eval_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:08:08.456792+00:00
-- url     : https://prove2.me/theorems/0b898ea0-804a-4aaa-9c9c-650b6e90363b
-- title:
--   Lemma alexander_eval_one from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_eval_one {N : ℕ} (hN : Odd N) : (alexander N).eval 1 = 1
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_eval_one {N : ℕ} (hN : Odd N) : (alexander N).eval 1 = 1
 := by sorry
