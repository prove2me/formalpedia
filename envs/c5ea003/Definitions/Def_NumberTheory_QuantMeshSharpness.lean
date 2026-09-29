-- Prove2me | Definitions.Def_NumberTheory_QuantMeshSharpness
-- name    : NumberTheory_QuantMeshSharpness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:17.437299+00:00
-- url     : https://prove2.me/theorems/ad8836fa-5d75-45e0-be4c-0e96441d48fc
-- title:
--   Aether Catalog definitions — NumberTheory_QuantMeshSharpness
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.QuantMeshSharpness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/QuantMeshSharpness.lean by skeleton subtraction
import Mathlib
/-
# Round-to-nearest meshes: exact defect constants, grouping, and non-transfer of a bit floor

This file is the formal shadow of the NET-52 experimental round
(*THE-TOY-FOUR-BIT-FLOOR-DOES-NOT-TRANSFER*).  The experiment measured the cross-entropy
damage of naive per-channel round-to-nearest (RTN) quantization of a pretrained transformer
at 2–8 bits, with and without grouping.  Four qualitative facts were observed:

* the damage is strictly monotone in the mesh and already nonzero at 8 bits;
* the constant in the mesh bound behaves as if it were *sharp* (no slack to exploit);
* grouping repairs a definite fraction of the damage;
* a "4-bit floor" calibrated on small from-scratch toys fails by more than an order of
  magnitude on pretrained weights.

Here we prove the underlying arithmetic statements, in a form that makes clear *why* the last
one is not a surprise but a theorem: the worst-case defect of an absmax `b`-bit quantizer is

`K · n · A / 2 ^ (b+1)`

and this is **attained**, so it depends on the amplitude `A` and the width `n` of the tensor,
never on the bit budget alone.  A floor stated in bits only is therefore empty: for every bit
budget and every prescribed budget `c` there is a weight vector exceeding it
(`toy_floor_does_not_transfer`).

Main results:

* `abs_rtn_sub_le` / `rtn_error_at_half` / `rtn_defect_constant_sharp` — the `Δ/2` mesh bound
  and its exact attainment (Mathlib's `round` breaks ties upwards).
* `mesh_succ`, `mesh_strictAnti` — one extra bit exactly halves the mesh.
* `l1_defect_le`, `l1_defect_sharp` — aggregate bound over a width-`n` tensor, attained.
* `lipschitz_defect_le`, `lipschitz_defect_sharp` — the `defect ≤ K n Δ/2` transfer bound with
  a matching witness, i.e. the constant cannot be improved.
* `grouped_defect_le_global`, `grouped_defect_lt_global` — grouping never hurts and strictly
  helps as soon as one group has smaller amplitude.
* `toy_floor_does_not_transfer` — no bits-only defect floor exists.
-/

namespace Catalog.NumberTheory.QuantMesh

open Finset

/-! ## The scalar quantizer -/

/-- Round-to-nearest quantization onto the mesh `Δ ℤ`. -/
noncomputable def rtn (Δ x : ℝ) : ℝ := Δ * round (x / Δ)

/-- The mesh of a `b`-bit absmax quantizer for a tensor of amplitude `A`. -/
noncomputable def mesh (A : ℝ) (b : ℕ) : ℝ := A / 2 ^ b









/-! ## Tensors: the aggregate defect -/



/-- Coordinatewise quantization with a (possibly coordinate-dependent) mesh. -/
noncomputable def quantVec {n : ℕ} (Δ : Fin n → ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => rtn (Δ i) (w i)




/-! ## Transfer through a Lipschitz loss -/



/-! ## Grouping -/




/-! ## No bits-only floor -/


end Catalog.NumberTheory.QuantMesh


