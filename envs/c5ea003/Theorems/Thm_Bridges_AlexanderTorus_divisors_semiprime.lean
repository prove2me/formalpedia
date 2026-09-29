-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_divisors_semiprime
-- name    : Bridges.AlexanderTorus.divisors_semiprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T14:49:18.183133+00:00
-- url     : https://prove2.me/theorems/40be75fa-e95e-4eb8-88d0-5550b7473e09
-- title:
--   Lemma divisors_semiprime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.divisors_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
--       (p * q).divisors = {1, p, q, p * q}
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.divisors_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q}
 := by sorry
