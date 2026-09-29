-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_semiprime_degree_sum
-- name    : Bridges.AlexanderTorus.alexander_semiprime_degree_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:26:14.489414+00:00
-- url     : https://prove2.me/theorems/8d55c6b4-18b8-4428-aa6d-fc65d726c0b9
-- title:
--   Lemma alexander_semiprime_degree_sum from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_semiprime_degree_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
--       (p - 1) + (q - 1) + (p - 1) * (q - 1) = p * q - 1
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_semiprime_degree_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p - 1) + (q - 1) + (p - 1) * (q - 1) = p * q - 1
 := by sorry
