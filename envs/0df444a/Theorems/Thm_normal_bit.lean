-- Prove2me | Theorems.Thm_normal_bit
-- name    : normal_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:48:05.722171+00:00
-- url     : https://prove2.me/theorems/317cdf76-8d45-4ef0-b142-beb69b76651e
-- title:
--   normal bit: normal bit
-- statement:
--   **Main theorem of this file.** Every 4-element set $\{0, a, b, c\}$ satisfying the
--   normalization conditions ($0 < a < b$, $a + b \le c$, $c \ge 289$, $\gcd(a, b, c) = 1$)
--   admits a 3-polychromatic coloring.
--
--   This is the entry point used by `Main.lean` to handle the large-c case. The proof
--   dispatches to `main_case_one` or `main_case_two` based on
--   $\min(\gcd(b, m), \gcd(b{-}a, m))$.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L134-L150
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi.lean#L134-L150

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Definitions.Def_Polychromatic_FourThree_Combi_CaseTwo
import Definitions.Def_Polychromatic_FourThree_Combi
set_option autoImplicit true
open Finset Pointwise

theorem normal_bit :
    ∀ a b c : ℤ, 0 < a → a < b → a + b ≤ c → 289 ≤ c → Finset.gcd {a, b, c} id = 1 →
          HasPolychromColouring (Fin 3) {0, a, b, c} := by sorry
