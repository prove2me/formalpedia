-- Prove2me | solution 1 for Catalog.NumberTheory.QuantMesh.lipschitz_defect_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T22:53:17.375972+00:00
-- url     : https://prove2.me/submissions/2ad442d3-7d66-45c7-b39f-973ce4c35c94

-- Sol generated from NumberTheory/QuantMeshSharpness.lean
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








/-- The bound is attained at the midpoint of a cell: Mathlib's `round` rounds ties up. -/
theorem rtn_error_at_half {Δ : ℝ} (hΔ : 0 < Δ) : rtn Δ (Δ / 2) - Δ / 2 = Δ / 2 := by
  have h : (Δ / 2) / Δ = 1 / 2 := by field_simp
  have hr : round ((Δ / 2) / Δ) = 1 := by
    rw [h]; norm_num
  simp only [rtn, hr]
  push_cast
  ring

/-- The midpoint is pushed to the top of its cell. -/
lemma rtn_at_half {Δ : ℝ} (hΔ : 0 < Δ) : rtn Δ (Δ / 2) = Δ := by
  have := rtn_error_at_half hΔ
  linarith


/-! ## Tensors: the aggregate defect -/

private lemma sum_const_fin (n : ℕ) (c : ℝ) : ∑ _i : Fin n, c = n * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma sum_const_half_fin (n : ℕ) (Δ : ℝ) : ∑ _i : Fin n, Δ / 2 = n * Δ / 2 := by
  rw [sum_const_fin]; ring





/-! ## Transfer through a Lipschitz loss -/



/-! ## Grouping -/




/-! ## No bits-only floor -/



open Catalog.NumberTheory.QuantMesh in
theorem solution(n : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ f : (Fin n → ℝ) → ℝ,
      (∀ u v : Fin n → ℝ, |f u - f v| ≤ 1 * ∑ i, |u i - v i|) ∧
      ∃ w : Fin n → ℝ, |f (quantVec (fun _ => Δ) w) - f w| = n * Δ / 2 := by
  refine ⟨fun u => ∑ i, u i, ?_, fun _ => Δ / 2, ?_⟩
  · intro u v
    rw [one_mul, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  · have hpt : ∀ i : Fin n, quantVec (n := n) (fun _ => Δ) (fun _ => Δ / 2) i = Δ := by
      intro i
      simpa [quantVec] using rtn_at_half hΔ
    show |∑ i, quantVec (n := n) (fun _ => Δ) (fun _ => Δ / 2) i - ∑ _i : Fin n, Δ / 2|
        = n * Δ / 2
    rw [Finset.sum_congr rfl fun i _ => hpt i, sum_const_fin, sum_const_half_fin]
    have h : (n:ℝ) * Δ - n * Δ / 2 = n * Δ / 2 := by ring
    rw [h, abs_of_nonneg (by positivity)]
