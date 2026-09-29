-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_totient_two_mul_of_odd
-- name    : Bridges.AlexanderTorus.totient_two_mul_of_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T15:15:36.193108+00:00
-- url     : https://prove2.me/theorems/ca5cc29e-9086-4721-9aec-e17e872f2a3f
-- title:
--   Lemma totient_two_mul_of_odd from the Aether Catalog (Bridges/AlexanderKnotNumberBridge)
-- statement:
--   Helper lemma from `Bridges.AlexanderTorus`.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.totient_two_mul_of_odd {n : ℕ} (hn : Odd n) : Nat.totient (2 * n) = Nat.totient n
--    := by sorry
--   ```

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem Bridges.AlexanderTorus.totient_two_mul_of_odd {n : ℕ} (hn : Odd n) : Nat.totient (2 * n) = Nat.totient n
 := by sorry
