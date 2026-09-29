-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_divisors_two_mul
-- name    : Bridges.AlexanderTorus.divisors_two_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T14:40:15.560515+00:00
-- url     : https://prove2.me/theorems/c6d29192-894c-4f22-acd3-9f0cb1176bb1
-- title:
--   Lemma divisors_two_mul from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.divisors_two_mul {N : ℕ} (hpos : 0 < N) :
--       (2 * N).divisors = N.divisors ∪ (N.divisors.image (fun d => 2 * d))
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.divisors_two_mul {N : ℕ} (hpos : 0 < N) :
    (2 * N).divisors = N.divisors ∪ (N.divisors.image (fun d => 2 * d))
 := by sorry
