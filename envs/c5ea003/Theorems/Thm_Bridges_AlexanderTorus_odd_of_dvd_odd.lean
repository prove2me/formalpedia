-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_odd_of_dvd_odd
-- name    : Bridges.AlexanderTorus.odd_of_dvd_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T14:25:20.966212+00:00
-- url     : https://prove2.me/theorems/2df12066-f2a1-41de-abdd-a92e285939f1
-- title:
--   A divisor of an odd number is odd
-- statement:
--   A divisor of an odd number is odd.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by sorry
--   ```
--
--   **Formalization Note** Helper lemma from the Aether Catalog source `Bridges/AlexanderKnotNumberBridge.lean` (namespace Bridges.AlexanderTorus); statement byte-identical to the source declaration.

import Mathlib

theorem Bridges.AlexanderTorus.odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by sorry
