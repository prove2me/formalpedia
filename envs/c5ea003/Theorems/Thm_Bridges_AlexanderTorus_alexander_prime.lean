-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_prime
-- name    : Bridges.AlexanderTorus.alexander_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:32:37.615455+00:00
-- url     : https://prove2.me/theorems/664cc351-cbfb-4d94-827e-d10cf584aeed
-- title:
--   Lemma alexander_prime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_prime {N : ℕ} (hN : Odd N) (hprime : N.Prime) :
--       alexander N = cyclotomic (2 * N) ℤ
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_prime {N : ℕ} (hN : Odd N) (hprime : N.Prime) :
    alexander N = cyclotomic (2 * N) ℤ
 := by sorry
