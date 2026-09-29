-- Prove2me | solution 1 for mme_CW_q6_primary_hash_Ctensor_outer_middle_fibers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:02:09.620833+00:00
-- url     : https://prove2.me/submissions/242b7b67-42bd-4848-8518-9d29b8a19dfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_primary_hash_induced_family_exists
import Theorems.Thm_mme_CW_q6_primary_hash_family_tensor_realization

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
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  have hfamilies :=
    mme_CW_q6_primary_hash_induced_family_exists tau htau
  filter_upwards [hfamilies] with N hfamilyN
  dsimp only at hfamilyN ⊢
  intro hconditions
  obtain ⟨A, H, family, hHbound, houter, hmiddle⟩ :=
    hfamilyN hconditions
  exact ⟨A, H, family.hHpos, hHbound,
    mme_CW_q6_primary_hash_family_tensor_realization
      (K := K) N _ _ A H family,
    houter, hmiddle⟩
