-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_natDegree_cyclotomic_two_mul_prime
-- name    : Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:18:29.883325+00:00
-- url     : https://prove2.me/theorems/9ca0a142-23de-4049-8cdb-523a53b3cb67
-- title:
--   Lemma natDegree_cyclotomic_two_mul_prime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_prime {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
--       (cyclotomic (2 * p) ℤ).natDegree = p - 1
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_prime {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    (cyclotomic (2 * p) ℤ).natDegree = p - 1
 := by sorry
