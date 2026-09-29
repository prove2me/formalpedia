-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_not_irreducible_of_not_prime
-- name    : Bridges.AlexanderTorus.alexander_not_irreducible_of_not_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:35:14.757894+00:00
-- url     : https://prove2.me/theorems/e23de479-768f-49ab-a17b-b4254c204892
-- title:
--   Lemma alexander_not_irreducible_of_not_prime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_not_irreducible_of_not_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N)
--       (hnp : ¬ N.Prime) : ¬ Irreducible (alexander N)
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_not_irreducible_of_not_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N)
    (hnp : ¬ N.Prime) : ¬ Irreducible (alexander N)
 := by sorry
