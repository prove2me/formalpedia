-- Prove2me | Theorems.Thm_gpy_fiberWeight_lamSelberg_le
-- name    : gpy_fiberWeight_lamSelberg_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:57.177481+00:00
-- url     : https://prove2.me/theorems/6792fadf-fdf5-4980-8733-730f409d1636
-- title:
--   Selberg fiber weight at L is at most tau_{k+1}(L)^2
-- statement:
--   For level R ≥ 2, the Selberg fiber weight at modulus L — the total |lambda_d lambda_e| over support pairs good at coordinate i with combined modulus L — is at most tau_{k+1}(L)^2: non-squarefree terms vanish by Möbius, and the surviving terms are at most 1 in absolute value, so the weight is bounded by the fiber count.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_fiberWeight_lamSelberg_le {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) (hR : 2 ≤ R) (i : Fin k) (L : ℕ) :
    ∑ p ∈ (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R)) ×ˢ
          ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R))).filter
        (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
      abs ((if ∏ i, p.1 i ≤ R then
            (ArithmeticFunction.moebius (∏ i, p.1 i) : ℝ)
              * (1 - Real.log ((∏ i, p.1 i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0)
          * (if ∏ i, p.2 i ≤ R then
            (ArithmeticFunction.moebius (∏ i, p.2 i) : ℝ)
              * (1 - Real.log ((∏ i, p.2 i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0))
      ≤ (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card : ℝ) ^ 2 := by sorry
