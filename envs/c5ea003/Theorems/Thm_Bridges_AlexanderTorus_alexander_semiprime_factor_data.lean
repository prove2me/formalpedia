-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_semiprime_factor_data
-- name    : Bridges.AlexanderTorus.alexander_semiprime_factor_data
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:23:35.042695+00:00
-- url     : https://prove2.me/theorems/ad907230-92cc-4488-ab33-0b76efd96398
-- title:
--   Lemma alexander_semiprime_factor_data from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_semiprime_factor_data {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
--       (cyclotomic (2 * p) ℤ).natDegree = p - 1 ∧
--       (cyclotomic (2 * q) ℤ).natDegree = q - 1 ∧
--       (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1) ∧
--       Irreducible (cyclotomic (2 * p) ℤ) ∧ Irreducible (cyclotomic (2 * q) ℤ) ∧
--       Irreducible (cyclotomic (2 * (p * q)) ℤ)
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.alexander_semiprime_factor_data {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * p) ℤ).natDegree = p - 1 ∧
    (cyclotomic (2 * q) ℤ).natDegree = q - 1 ∧
    (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1) ∧
    Irreducible (cyclotomic (2 * p) ℤ) ∧ Irreducible (cyclotomic (2 * q) ℤ) ∧
    Irreducible (cyclotomic (2 * (p * q)) ℤ)
 := by sorry
