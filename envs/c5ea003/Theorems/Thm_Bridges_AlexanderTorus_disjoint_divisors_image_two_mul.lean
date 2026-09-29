-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_disjoint_divisors_image_two_mul
-- name    : Bridges.AlexanderTorus.disjoint_divisors_image_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T14:41:51.355642+00:00
-- url     : https://prove2.me/theorems/cc996fe8-cc41-4626-bb33-331a7d31715e
-- title:
--   Lemma disjoint_divisors_image_two_mul from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.disjoint_divisors_image_two_mul {N : ℕ} (hN : Odd N) :
--       Disjoint N.divisors (N.divisors.image (fun d => 2 * d))
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.disjoint_divisors_image_two_mul {N : ℕ} (hN : Odd N) :
    Disjoint N.divisors (N.divisors.image (fun d => 2 * d))
 := by sorry
