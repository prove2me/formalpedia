-- Prove2me | Theorems.Thm_ToricCode_d1_ne_zero_iff
-- name    : ToricCode.d1_ne_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:31:20.916683+00:00
-- url     : https://prove2.me/theorems/4f937918-3921-42ee-a844-95d0879d6a70
-- title:
--   Incidence criterion for the vertex boundary map.
-- statement:
--   Incidence criterion for the vertex boundary map.
--
--   ```lean
--   theorem ToricCode.d1_ne_zero_iff(v : Vert M N) (b : Bool) (u : ZMod M × ZMod N) :
--       d1 M N v (b, u) ≠ 0 ↔ (u = v ∨ u = v - step M N b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Locality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Locality.lean#L45

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


omit [NeZero M] [NeZero N] in

theorem ToricCode.d1_ne_zero_iff(v : Vert M N) (b : Bool) (u : ZMod M × ZMod N) :
    d1 M N v (b, u) ≠ 0 ↔ (u = v ∨ u = v - step M N b) := by sorry
