-- Prove2me | Theorems.Thm_NewtonTropical_padicVal_add_of_ne
-- name    : NewtonTropical.padicVal_add_of_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:23:10.070793+00:00
-- url     : https://prove2.me/theorems/3968c336-a670-46a8-a4a3-fdc7aef55514
-- title:
--   The Newton polygon phenomenon.
-- statement:
--   **The Newton polygon phenomenon.**  When the two valuations differ, the tropical
--   inequality becomes an equality: the lowest vertex of the Newton polygon is
--   determined by the unique minimizing term.
--
--   ```lean
--   theorem NewtonTropical.padicVal_add_of_ne(hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
--       (hne : val p a ≠ val p b) : val p (a + b) = min (val p a) (val p b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Newtontropicalbridge/NewtonTropicalBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Newtontropicalbridge/NewtonTropicalBridge.lean#L89

-- Thm stub generated from Combinatorics/Newtontropicalbridge/NewtonTropicalBridge.lean
import Mathlib
import Definitions.Def_Combinatorics_Newtontropicalbridge_NewtonTropicalBridge

/-!
# The Newton–tropical bridge

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/NewtonTropicalBridge.lean`.  It is reconstructed here as
a self-contained account of the bridge between *`p`-adic valuations* (the data
recorded by a Newton polygon) and the *tropical (min-plus) semiring*.

The bridge is the statement that `v_p : ℕ_{>0} → ℕ` intertwines the ordinary
arithmetic operations with the tropical ones:

| ordinary | tropical |
|----------|----------|
| `a * b`  | `v a + v b`   (`padicVal_mul`) |
| `a + b`  | `min (v a) (v b)` (`min_le_padicVal_add`, with equality in `padicVal_add_of_ne`) |

Main results:

* `NewtonTropical.padicVal_mul` — multiplicativity;
* `NewtonTropical.min_le_padicVal_add` — the ultrametric (tropical) inequality;
* `NewtonTropical.padicVal_add_of_ne` — the *Newton polygon* phenomenon: the
  inequality is an equality whenever the two valuations differ;
* `NewtonTropical.padicVal_pow`, `NewtonTropical.padicVal_prod` — the tropical
  power and product rules;
* `NewtonTropical.newton_slope_min` — the lowest Newton slope of a two-term sum.
-/

open NewtonTropical

open Nat

variable {p : ℕ}




/-! ## Tropical multiplication -/




/-! ## Tropical addition -/

theorem NewtonTropical.padicVal_add_of_ne(hp : p.Prime) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : val p a ≠ val p b) : val p (a + b) = min (val p a) (val p b) := by sorry
