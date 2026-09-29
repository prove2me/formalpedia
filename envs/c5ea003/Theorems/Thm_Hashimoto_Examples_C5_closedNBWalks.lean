-- Prove2me | Theorems.Thm_Hashimoto_Examples_C5_closedNBWalks
-- name    : Hashimoto.Examples.C5_closedNBWalks
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:34:43.209249+00:00
-- url     : https://prove2.me/theorems/2538b12a-8d39-441c-ab86-0263b872ea6a
-- title:
--   The pentagon has `10` rooted closed non-backtracking walks of every length divisible
-- statement:
--   The pentagon has `10` rooted closed non-backtracking walks of every length divisible
--   by `5` (five rotations times two orientations) and none of any other positive length.
--
--   ```lean
--   theorem Hashimoto.Examples.C5_closedNBWalks(n : ℕ) (hn : 1 ≤ n) :
--       (closedNBWalks C5 n).card = if 5 ∣ n then 10 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/Examples.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/Examples.lean#L108

-- Thm stub generated from Algebra/NonBacktracking/Examples.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_Examples
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace

/-!
# Worked examples of the non-backtracking trace formula

Concrete graphs on which the counting theorem
`trace (B ^ n) = #{rooted closed non-backtracking walks of length n}` is exercised.

* the **triangle** `K₃`: its Hashimoto matrix is a permutation matrix of order `3`
  (`Hashimoto.Examples.K3_hashimoto_pow_three`), whence the exact periodic count
  `trace (B ^ n) = 6` if `3 ∣ n` and `0` otherwise;
* the **complete graph** `K₄`: `trace (B³) = 24 = 6 · 4` (four triangles) and
  `trace (B⁴) = 24 = 8 · 3` (three quadrilaterals);
* the **path** `P₃`, a tree: `B² = 0`, so a tree has no closed non-backtracking walk
  of any length.

All numeric statements are checked by kernel evaluation (`decide`) and then combined
with the general theorems, so no example is a bare computation.
-/

open Hashimoto.Examples

open Hashimoto

/-! ## The triangle -/


instance : DecidableRel K3.Adj := fun a b => by unfold K3; infer_instance







/-! ## The complete graph on four vertices -/


instance : DecidableRel K4.Adj := fun a b => by unfold K4; infer_instance



/-! ## The pentagon -/


instance : DecidableRel C5.Adj := fun a b => by unfold C5 SimpleGraph.fromRel; infer_instance

theorem Hashimoto.Examples.C5_closedNBWalks(n : ℕ) (hn : 1 ≤ n) :
    (closedNBWalks C5 n).card = if 5 ∣ n then 10 else 0 := by sorry
