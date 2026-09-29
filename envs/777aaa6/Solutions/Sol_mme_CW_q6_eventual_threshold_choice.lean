-- Prove2me | solution 1 for mme_CW_q6_eventual_threshold_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T01:30:37.427442+00:00
-- url     : https://prove2.me/submissions/8c9797b5-023d-4fbb-a298-d251b5e028fe

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Explicit integer thresholds for the strict q=6 collision margin. -/
theorem solution
    {B M S Z : ℕ} (hM : 0 < M) (hlarge : 400 * M ≤ B) :
    let K := (3 * B) / (4 * M)
    let H := B / (8 * M)
    let R := B / 4
    let Q := (S * Z) / (16 * M)
    0 < R ∧
      H ≤ K ∧
      M * K + R ≤ B ∧
      16 * B * M ≤ R ^ 2 ∧
      5 * B ≤ 8 * M * (K - H + 1) ∧
      16 * M * Q ≤ S * Z := by
  dsimp only
  let d : ℕ := 8 * M
  let K : ℕ := (3 * B) / (4 * M)
  let H : ℕ := B / d
  let R : ℕ := B / 4
  have hd : 0 < d := by simp [d, hM]
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity : 0 < 400 * M) hlarge
  have hRpos : 0 < R := by
    exact Nat.div_pos (by omega) (by norm_num)
  have hKrewrite : K = (6 * B) / d := by
    dsimp only [K, d]
    have hscale := Nat.mul_div_mul_left (3 * B) (4 * M)
      (by norm_num : 0 < 2)
    calc
      3 * B / (4 * M) = 2 * (3 * B) / (2 * (4 * M)) := hscale.symm
      _ = 6 * B / (8 * M) := by congr 1 <;> omega
  have hHmul : d * H ≤ B := by
    simpa only [H] using Nat.mul_div_le B d
  have h6lt : 6 * B < d * (K + 1) := by
    rw [hKrewrite]
    exact Nat.lt_mul_div_succ (6 * B) hd
  have hHK : H ≤ K := by
    by_contra hnot
    have hk1 : K + 1 ≤ H := by omega
    have hmul := Nat.mul_le_mul_left d hk1
    nlinarith
  have hDmargin : 5 * B ≤ d * (K - H + 1) := by
    have h6lt' : 6 * B < d * K + d := by
      simpa [Nat.mul_add] using h6lt
    have hmulHK : d * H ≤ d * K := Nat.mul_le_mul_left d hHK
    have h5lt : 5 * B < d * (K - H + 1) := by
      rw [Nat.mul_add, Nat.mul_sub_left_distrib]
      omega
    exact h5lt.le
  have hKmul4 : 4 * (M * K) ≤ 3 * B := by
    have h := Nat.mul_div_le (3 * B) (4 * M)
    change 4 * M * K ≤ 3 * B at h
    convert h using 1 <;> ring
  have hRmul4 : 4 * R ≤ B := by
    simpa only [R, Nat.mul_comm] using Nat.mul_div_le B 4
  have hgap : M * K + R ≤ B := by omega
  have hB_R : B ≤ 5 * R := by
    dsimp only [R]
    omega
  have hRmargin : 16 * B * M ≤ R ^ 2 := by
    have hBM : 400 * B * M ≤ B ^ 2 := by
      nlinarith
    have hBRsq : B ^ 2 ≤ 25 * R ^ 2 := by
      nlinarith
    nlinarith
  have hQ : 16 * M * ((S * Z) / (16 * M)) ≤ S * Z := by
    simpa only using Nat.mul_div_le (S * Z) (16 * M)
  refine ⟨hRpos, ?_, ?_, hRmargin, ?_, hQ⟩
  · simpa only [K, H, d] using hHK
  · simpa only [K, R] using hgap
  · simpa only [K, H, d] using hDmargin

