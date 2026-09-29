-- Prove2me | Theorems.Thm_ToricCode_qubit_X_degree_eq_two
-- name    : ToricCode.qubit_X_degree_eq_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:33:33.606233+00:00
-- url     : https://prove2.me/theorems/468f3e8e-9127-436d-8adf-611665c2e1bf
-- title:
--   Every qubit meets exactly two `X`-checks — the two faces it separates.
-- statement:
--   **Every qubit meets exactly two `X`-checks** — the two faces it separates.
--
--   ```lean
--   theorem ToricCode.qubit_X_degree_eq_two(e : Edge M N) : (xChecks M N e).card = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Locality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Locality.lean#L207

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





/-! ### Qubit degrees -/

theorem ToricCode.qubit_X_degree_eq_two(e : Edge M N) : (xChecks M N e).card = 2 := by sorry
