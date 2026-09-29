-- Prove2me | Theorems.Thm_Catalog_NumberTheory_QuantMesh_lipschitz_defect_sharp
-- name    : Catalog.NumberTheory.QuantMesh.lipschitz_defect_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:27:29.486794+00:00
-- url     : https://prove2.me/theorems/191f1fc3-9227-466d-b7a8-4bfb3f1e0df9
-- title:
--   The transfer constant is sharp.
-- statement:
--   **The transfer constant is sharp.**  For every width and mesh there is a `1`-Lipschitz loss
--   and a weight tensor for which the bound `n Δ / 2` holds with equality.
--
--   ```lean
--   theorem Catalog.NumberTheory.QuantMesh.lipschitz_defect_sharp(n : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
--       ∃ f : (Fin n → ℝ) → ℝ,
--         (∀ u v : Fin n → ℝ, |f u - f v| ≤ 1 * ∑ i, |u i - v i|) ∧
--         ∃ w : Fin n → ℝ, |f (quantVec (fun _ => Δ) w) - f w| = n * Δ / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuantMeshSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuantMeshSharpness.lean#L147

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

theorem Catalog.NumberTheory.QuantMesh.lipschitz_defect_sharp(n : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ f : (Fin n → ℝ) → ℝ,
      (∀ u v : Fin n → ℝ, |f u - f v| ≤ 1 * ∑ i, |u i - v i|) ∧
      ∃ w : Fin n → ℝ, |f (quantVec (fun _ => Δ) w) - f w| = n * Δ / 2 := by sorry
