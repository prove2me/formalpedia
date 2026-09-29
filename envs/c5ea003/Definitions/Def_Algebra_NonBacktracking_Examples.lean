-- Prove2me | Definitions.Def_Algebra_NonBacktracking_Examples
-- name    : Algebra_NonBacktracking_Examples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:25.001928+00:00
-- url     : https://prove2.me/theorems/ea68f282-3d98-49d7-8220-b719e4fbaa2a
-- title:
--   Aether Catalog definitions — Algebra_NonBacktracking_Examples
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NonBacktracking.Examples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NonBacktracking/Examples.lean by skeleton subtraction
import Mathlib
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

namespace Hashimoto.Examples

open Hashimoto

/-! ## The triangle -/

/-- The triangle `K₃`. -/
def K3 : SimpleGraph (Fin 3) := ⊤

instance : DecidableRel K3.Adj := fun a b => by unfold K3; infer_instance







/-! ## The complete graph on four vertices -/

/-- The complete graph `K₄`. -/
def K4 : SimpleGraph (Fin 4) := ⊤

instance : DecidableRel K4.Adj := fun a b => by unfold K4; infer_instance



/-! ## The pentagon -/

/-- The cycle graph `C₅`. -/
def C5 : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun u v => (u.val + 1) % 5 = v.val

instance : DecidableRel C5.Adj := fun a b => by unfold C5 SimpleGraph.fromRel; infer_instance






/-! ## A tree -/

/-- The path `0 — 1 — 2`. -/
def P3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun u v => u.val + 1 = v.val

instance : DecidableRel P3.Adj := fun a b => by unfold P3 SimpleGraph.fromRel; infer_instance



end Hashimoto.Examples


