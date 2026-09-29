-- Prove2me | Theorems.Thm_Catalog_NumberTheory_QuantMesh_toy_floor_does_not_transfer
-- name    : Catalog.NumberTheory.QuantMesh.toy_floor_does_not_transfer
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:24:21.720191+00:00
-- url     : https://prove2.me/theorems/b6ad8eba-864a-4737-81a7-8bbda85df5d5
-- title:
--   THE-TOY-FOUR-BIT-FLOOR-DOES-NOT-TRANSFER (formal form).
-- statement:
--   **THE-TOY-FOUR-BIT-FLOOR-DOES-NOT-TRANSFER (formal form).**
--
--   For *every* bit budget `b` and every prescribed damage budget `c`, there is an amplitude `A`
--   and a weight tensor of that amplitude on which the `b`-bit absmax RTN quantizer makes a
--   `1`-Lipschitz loss move by more than `c`.  Hence no statement of the form "`b` bits cost at
--   most `c`" can be a theorem: any such floor is a statement about the amplitude (and width) of
--   the particular tensors it was calibrated on, not about the bit budget.
--
--   ```lean
--   theorem Catalog.NumberTheory.QuantMesh.toy_floor_does_not_transfer(b : ℕ) (c : ℝ) :
--       ∃ (A : ℝ) (w : Fin 1 → ℝ) (f : (Fin 1 → ℝ) → ℝ),
--         0 < A ∧ (∀ u v : Fin 1 → ℝ, |f u - f v| ≤ 1 * ∑ i, |u i - v i|) ∧
--         (∀ i, |w i| ≤ A) ∧
--         c < |f (quantVec (fun _ => mesh A b) w) - f w| := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuantMeshSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuantMeshSharpness.lean#L196

-- Thm stub generated from NumberTheory/QuantMeshSharpness.lean
import Mathlib
import Definitions.Def_NumberTheory_QuantMeshSharpness
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

open Catalog.NumberTheory.QuantMesh

open Finset

/-! ## The scalar quantizer -/











/-! ## Tensors: the aggregate defect -/







/-! ## Transfer through a Lipschitz loss -/



/-! ## Grouping -/




/-! ## No bits-only floor -/

theorem Catalog.NumberTheory.QuantMesh.toy_floor_does_not_transfer(b : ℕ) (c : ℝ) :
    ∃ (A : ℝ) (w : Fin 1 → ℝ) (f : (Fin 1 → ℝ) → ℝ),
      0 < A ∧ (∀ u v : Fin 1 → ℝ, |f u - f v| ≤ 1 * ∑ i, |u i - v i|) ∧
      (∀ i, |w i| ≤ A) ∧
      c < |f (quantVec (fun _ => mesh A b) w) - f w| := by sorry
