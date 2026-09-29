-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:45:09.655887+00:00
-- url     : https://prove2.me/submissions/afb24055-8fe0-468d-97ff-131da7c82a09

import Mathlib
import Theorems.Thm_mme_CW_q6_collision_margin_arithmetic
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution
    {n L G K H R Q : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (hHK : H ≤ K) (hR : 0 < R)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1))
    (hgap :
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1) * K + R ≤
        Nat.choose (2 * G) G)
    (hRmargin :
      16 * Nat.choose (2 * G) G *
          (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤ R ^ 2)
    (hDmargin :
      5 * Nat.choose (2 * G) G ≤
        8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) *
          (K - H + 1))
    (hQmargin :
      16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) * Q ≤
        S.card * (cwQ6ExactZWords (n + 1) L G).card) :
    ∃ w : Fin (2 * n + 2) →
          ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
      ∃ b0 : ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
        ∃ I : Finset (CWQ6ExactCoupledAddress (n + 1) L G),
          I ⊆ cwQ6PrimaryHashBucket (n + 1) L G
              (Nat.choose (n + 1) G) S b0 w ∧
          (∀ e ∈ I,
            ∀ e' ∈ cwQ6PrimaryHashBucket (n + 1) L G
                (Nat.choose (n + 1) G) S b0 w,
              (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
          Q ≤ ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
            H ≤ (I.filter (fun e => e.1 2 = z)).card)).card := by
  let X : ℕ := Nat.choose (n + 1) G
  let B : ℕ := Nat.choose (2 * G) G
  let M : ℕ := 4 * X ^ 2 + 1
  let Z : Finset (Fin (2 * (n + 1)) → Fin 3) :=
    cwQ6ExactZWords (n + 1) L G
  change 16 * B * M ≤ R ^ 2 at hRmargin
  change 5 * B ≤ 8 * M * (K - H + 1) at hDmargin
  change 16 * M * Q ≤ S.card * Z.card at hQmargin
  have hXM : 4 * X ^ 2 ≤ M := by
    dsimp [M]
    omega
  have hbase := mme_CW_q6_collision_margin_arithmetic
    (B := B) (M := M) (X := X) (D := K - H + 1)
    (R := R) (Q := Q) (S := S.card) (Z := Z.card)
    hXM hRmargin hDmargin hQmargin
  have hscaled := Nat.mul_le_mul_left (M ^ (2 * n)) hbase
  have hpow3 : M ^ (2 * n) * M ^ 3 = M ^ (2 * n + 3) := by
    rw [← pow_add]
  have hpow2 : M ^ (2 * n) * M ^ 2 = M ^ (2 * n + 2) := by
    rw [← pow_add]
  have harith :
      M ^ (2 * n + 3) * ((K - H + 1) * R ^ 2 * Q) +
            R ^ 2 *
              (2 * (Z.card * B) * X ^ 2 * S.card * M ^ (2 * n)) +
            (K - H + 1) *
              (2 * B * M ^ (2 * n + 3) * S.card * Z.card) ≤
          (K - H + 1) *
            (R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card) := by
    calc
      _ = M ^ (2 * n) *
          (M ^ 3 * (K - H + 1) * R ^ 2 * Q +
            R ^ 2 * (2 * Z.card * B * X ^ 2 * S.card) +
            (K - H + 1) * (2 * B * M ^ 3 * S.card * Z.card)) := by
        rw [← hpow3]
        ring
      _ ≤ M ^ (2 * n) *
          ((K - H + 1) * R ^ 2 * M ^ 2 * S.card * Z.card) := hscaled
      _ = (K - H + 1) *
          (R ^ 2 * M ^ (2 * n + 2) * S.card * Z.card) := by
        rw [← hpow2]
        ring
  exact
    mme_CW_q6_regular_primary_hash_bucket_weighted_isolated_many_z_stars
      hregular hG hHK hR S
        (by simpa only [M, X] using hSrange)
        (by simpa only [M, X, B] using hgap)
        (by simpa only [M, X, B, Z] using harith)
