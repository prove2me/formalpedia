-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_ne_zero
-- name    : Bridges.AlexanderTorus.alexander_ne_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:02:49.772166+00:00
-- url     : https://prove2.me/theorems/bd22219c-8e9a-41e7-81f8-ae1ca613e81d
-- title:
--   Lemma alexander_ne_zero from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_ne_zero {N : ℕ} (hN : Odd N) : alexander N ≠ 0
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_ne_zero {N : ℕ} (hN : Odd N) : alexander N ≠ 0
 := by sorry
