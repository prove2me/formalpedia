-- Prove2me | Definitions.Def_Geometry_ToricCode_Locality
-- name    : Geometry_ToricCode_Locality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:27:03.603645+00:00
-- url     : https://prove2.me/theorems/17ed3a38-ff2e-4532-ba56-4febb1dac821
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_Locality
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.Locality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/Locality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
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

open Matrix

namespace ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]

section Local

variable (hM : 2 ≤ M) (hN : 2 ≤ N)

include hM hN




/-! ### Check weights -/

/-- The qubits acted on by the `Z`-check at the vertex `v`. -/
def zSupport (v : Vert M N) : Finset (Edge M N) :=
  Finset.univ.filter (fun e => d1 M N v e ≠ 0)


/-- The qubits acted on by the `X`-check at the face `f`. -/
def xSupport (f : Face M N) : Finset (Edge M N) :=
  Finset.univ.filter (fun e => d2 M N e f ≠ 0)


/-! ### Qubit degrees -/

/-- The `Z`-checks acting on the qubit `e`. -/
def zChecks (e : Edge M N) : Finset (Vert M N) :=
  Finset.univ.filter (fun v => d1 M N v e ≠ 0)


/-- The `X`-checks acting on the qubit `e`. -/
def xChecks (e : Edge M N) : Finset (Face M N) :=
  Finset.univ.filter (fun f => d2 M N e f ≠ 0)



end Local

end ToricCode


