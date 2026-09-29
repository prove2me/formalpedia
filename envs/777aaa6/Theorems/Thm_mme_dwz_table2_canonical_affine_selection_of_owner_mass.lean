-- Prove2me | Theorems.Thm_mme_dwz_table2_canonical_affine_selection_of_owner_mass
-- name    : mme_dwz_table2_canonical_affine_selection_of_owner_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T00:06:02.204287+00:00
-- url     : https://prove2.me/theorems/f54a5fe8-18a5-4c66-b445-01375b6c68e5
-- title:
--   One canonical affine state preserves aggregate owner mass
-- statement:
--   Let T be a target family inside an ambient Table-2 family A, and let each affine state assign a bounded nonnegative integer mass to every target owner. Assume that for every owner, the total mass over states whose canonical affine bucket contains that owner is at least seven eighths of the full label-weight capacity. If the X- and Y-degrees of T in A are bounded by d and 8d≤p, then one affine state q contains an X/Y-isolated subfamily I whose normalized retained mass is at least |T||S|/(2p^2). This is the exact finite double-counting step that converts ownerwise Claim-6.8 mass into one shared state.
-- source:
--   Duan--Wu--Zhou, weighted form of the asymmetric first-hash selection underlying Equation (24).

import Theorems.Thm_mme_dwz_table2_canonical_affine_weighted_aggregate_selection

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_canonical_affine_selection_of_owner_mass
    {p N : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d cap : ℕ) (hcap : 0 < cap) (hmod : 8 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeX (b t)) =
          (fun t ↦ DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ DWZSquare.shapeY (b t)) =
          (fun t ↦ DWZSquare.shapeY (a t)))).card ≤ d)
    (mass : ((Fin (N + 2) → ZMod p) × ZMod p) →
      (Fin (N + 1) → Fin 15) → ℕ)
    (hmassCap : ∀ q a, a ∈ T →
      a ∈ dwzTable2AffineHashBucket S A q → mass q a ≤ cap)
    (howner : ∀ a ∈ T,
      7 * S.card * p ^ (N + 1) * cap ≤
        8 * ∑ q ∈ (Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦
          a ∈ dwzTable2AffineHashBucket S A q)),
          mass q a) :
    ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
      ∃ I : Finset (Fin (N + 1) → Fin 15),
        I ⊆ T ∧
        I ⊆ dwzTable2AffineHashBucket S A q ∧
        (∀ e ∈ I, ∀ e' ∈ dwzTable2AffineHashBucket S A q,
          (fun t ↦ DWZSquare.shapeX (e t)) =
              (fun t ↦ DWZSquare.shapeX (e' t)) ∨
            (fun t ↦ DWZSquare.shapeY (e t)) =
              (fun t ↦ DWZSquare.shapeY (e' t)) → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤
          ∑ a ∈ I, (mass q a : ℝ) / (cap : ℝ) := by

  sorry
