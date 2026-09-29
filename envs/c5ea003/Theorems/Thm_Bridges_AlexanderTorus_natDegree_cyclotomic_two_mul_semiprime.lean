-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_natDegree_cyclotomic_two_mul_semiprime
-- name    : Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_semiprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:20:28.442431+00:00
-- url     : https://prove2.me/theorems/f8a0303d-e835-48d1-9a36-9ccb4e7ef594
-- title:
--   Lemma natDegree_cyclotomic_two_mul_semiprime from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
--       (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1)
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.natDegree_cyclotomic_two_mul_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1)
 := by sorry
