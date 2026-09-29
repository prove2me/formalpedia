-- Prove2me | solution 1 for mme_CW_q6_primary_hash_Ctensor_finite_capacity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:44:47.598316+00:00
-- url     : https://prove2.me/submissions/17c3b5cf-635b-4a44-aa09-110bd8f524a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
import Theorems.Thm_mme_CW_q6_primary_capacity_of_outer_middle_fibers

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L Gcount)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        capacity * Real.exp (-((N : ℝ) * loss / 2)) ≤
          ((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2) := by
  have hcore :=
    mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
      (K := K) tau htau
  filter_upwards [hcore] with N hcoreN
  dsimp only at hcoreN ⊢
  intro hconditions
  obtain ⟨A, H, hHpos, hHbound, hrestrict, houter, hmiddle⟩ :=
    hcoreN hconditions
  refine ⟨A, H, hHpos, hHbound, hrestrict, ?_⟩
  have hGle :
      N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊ ≤ N :=
    Nat.sub_le _ _
  have hXpos :
      0 < Nat.choose N
        (N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊) :=
    Nat.choose_pos hGle
  exact mme_CW_q6_primary_capacity_of_outer_middle_fibers
    N
    (Nat.choose (2 * N)
        ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊ *
      Nat.choose
        (2 * N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊)
        ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊)
    (Nat.choose N
      (N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊))
    (Nat.choose
      (2 * (N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊))
      (N - ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊))
    A H
    (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
    hXpos houter hmiddle
