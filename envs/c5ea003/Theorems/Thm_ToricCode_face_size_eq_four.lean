-- Prove2me | Theorems.Thm_ToricCode_face_size_eq_four
-- name    : ToricCode.face_size_eq_four
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:31:32.170644+00:00
-- url     : https://prove2.me/theorems/a860a182-de42-4062-9258-9f14e3d6fc40
-- title:
--   Every `X`-stabilizer has weight `4`.
-- statement:
--   **Every `X`-stabilizer has weight `4`.**
--
--   ```lean
--   theorem ToricCode.face_size_eq_four(f : Face M N) : (xSupport M N f).card = 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Locality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Locality.lean#L128

-- Thm stub generated from Geometry/ToricCode/Locality.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Locality
/-!
# Bounded local geometry of the square torus cellulation

The previous research cycle explicitly flagged that its counterexamples were
*not* claimed to come from bounded-degree local cellulations, and listed
"bounded face size and bounded vertex degree" as a missing ingredient.  This
file supplies exactly that data for the square torus, for every `M, N ≥ 2`:

* `vertex_degree_eq_four` : every `Z`-stabilizer (vertex) acts on exactly `4`
  qubits;
* `face_size_eq_four` : every `X`-stabilizer (face) acts on exactly `4` qubits;
* `qubit_Z_degree_eq_two` and `qubit_X_degree_eq_two` : every qubit is touched
  by exactly `2` checks of each type.

Hence the toric code is an LDPC code with all check weights and qubit degrees
bounded by `4`, uniformly in `M` and `N`.  Combined with `ToricCode.Distance` this makes
the family a genuine geometric witness: bounded local geometry, fixed genus one,
and unbounded distance.
-/

-- open removed: section is not a namespace

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]


variable (hM : 2 ≤ M) (hN : 2 ≤ N)

include hM hN




/-! ### Check weights -/

theorem ToricCode.face_size_eq_four(f : Face M N) : (xSupport M N f).card = 4 := by sorry
