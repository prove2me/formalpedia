-- Prove2me | solution 1 for mme_CW_q6_shared_xy_pair_hash_parameter_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:07:40.793803+00:00
-- url     : https://prove2.me/submissions/b1706df1-2817-4c11-9209-a7f7dee408bd

import Mathlib
import Theorems.Thm_mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card
import Theorems.Thm_mme_CW_q6_z_hash_offset_label_card

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A fixed distinct X/Y-collision pair survives its two difference equations
and one retained affine Z-label for exactly `|S| M^(2n)` parameters. -/
theorem solution
    {M n L G : ℕ} [NeZero M]
    (h2 : IsUnit (2 : ZMod M))
    (e f : CWQ6ExactCoupledAddress (n + 1) L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range M) :
    let c : CWQ6ExactCoupledAddress (n + 1) L G →
        Fin (2 * n + 2) → ZMod M := fun a j =>
      (2 * ((a.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
    (((Finset.univ : Finset
        ((Fin (2 * n + 2) → ZMod M) × ZMod M)).filter (fun ω =>
      (∑ i, c e i * ω.1 i = 0) ∧
      (∑ i, c f i * ω.1 i = 0) ∧
      ∃ s ∈ S,
        cwQ6DoubledZHash ω.2 ω.1 (e.1 2) =
          2 * (s : ZMod M))).card) = S.card * M ^ (2 * n) := by
  classical
  let c : CWQ6ExactCoupledAddress (n + 1) L G →
      Fin (2 * n + 2) → ZMod M := fun a j =>
    (2 * ((a.1 0 j).val : ZMod M)) -
      (cwQ6CoupledZHashCode (a.1 2 j) : ZMod M)
  have hminorRaw := mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
    (M := M) e f hne hshare
  have hminor : ∃ j k : Fin (2 * n + 2),
      IsUnit (c e j * c f k - c e k * c f j) := by
    simpa only [c, show 2 * (n + 1) = 2 * n + 2 by omega] using hminorRaw
  obtain ⟨j, k, hjk⟩ := hminor
  let Good : (Fin (2 * n + 2) → ZMod M) → Prop := fun w =>
    (∑ i, c e i * w i = 0) ∧ (∑ i, c f i * w i = 0)
  let Label : (Fin (2 * n + 2) → ZMod M) → ZMod M → Prop := fun w b0 =>
    ∃ s ∈ S,
      cwQ6DoubledZHash b0 w (e.1 2) = 2 * (s : ZMod M)
  have hGoodCard :
      ((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter Good).card =
        M ^ (2 * n) := by
    simpa only [Good] using mme_ZMod_two_linear_hash_fiber_card
      (M := M) (n := 2 * n) (c e) (c f) j k hjk 0 0
  have hLabelCard (w : Fin (2 * n + 2) → ZMod M) :
      ((Finset.univ : Finset (ZMod M)).filter (Label w)).card = S.card := by
    simpa only [Label, show 2 * (n + 1) = 2 * n + 2 by omega] using
      mme_CW_q6_z_hash_offset_label_card h2 S hSrange w (e.1 2)
  dsimp only
  simp only [← and_assoc]
  change ((Finset.univ.filter (fun ω :
      (Fin (2 * n + 2) → ZMod M) × ZMod M =>
        Good ω.1 ∧ Label ω.1 ω.2)).card) = _
  rw [Finset.card_filter]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  have hinner (w : Fin (2 * n + 2) → ZMod M) :
      (∑ b0 ∈ (Finset.univ : Finset (ZMod M)),
          if Good w ∧ Label w b0 then 1 else 0) =
        if Good w then S.card else 0 := by
    by_cases hw : Good w
    · simp only [hw, true_and, if_true]
      rw [← Finset.card_filter, hLabelCard]
    · simp [hw]
  rw [Finset.sum_congr rfl (fun w _ => hinner w)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, Nat.nsmul_eq_mul]
  rw [hGoodCard]
  exact Nat.mul_comm _ _
