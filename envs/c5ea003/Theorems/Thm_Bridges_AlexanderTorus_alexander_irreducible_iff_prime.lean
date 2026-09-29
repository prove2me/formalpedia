-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_irreducible_iff_prime
-- name    : Bridges.AlexanderTorus.alexander_irreducible_iff_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:41:24.476488+00:00
-- url     : https://prove2.me/theorems/8d2764de-6005-43c7-8300-c77196ef4a0d
-- title:
--   Lemma alexander_irreducible_iff_prime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_irreducible_iff_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N) :
--       Irreducible (alexander N) ↔ N.Prime
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_irreducible_iff_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N) :
    Irreducible (alexander N) ↔ N.Prime
 := by sorry
