-- Prove2me | solution 1 for CyclicCubic.mutualInfo_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:16:00.520561+00:00
-- url     : https://prove2.me/submissions/a75e06a0-18f5-4a5c-8192-f60bef2b356b

/-
# `CyclicCubic.mutualInfo_semiprime`
Target `339c7ada` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by the toolchain selftest.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`MI w = H(marginal_α) + H(marginal_β) - H(joint)`. With `L = logb 2 3`:
  marginal over k  :  0 once, 1/6 six times      ->  H = 1 + L
  marginal over n  :  4/9, 4/9, 1/9              ->  H = 2L - 16/9
  joint            :  (this is target 30c0c5bc)  ->  H = 2L + 1/3
  MI = (1 + L) + (2L - 16/9) - (2L + 1/3) = L - 10/9.
Checked symbolically over ℚ[L] and numerically: both agree exactly (diff 0.0e+00).

Reuses the two presentation fixes established on 30c0c5bc:
  * arity-specific `Fin.sum_univ_seven` / `Fin.sum_univ_three` ALONE — never alongside
    `Fin.sum_univ_succ`, which shadows them and leaves `Fin.succ` towers instead of numerals;
  * count hypotheses stated at `Fin 7`, because the `show` retypes the `ZMod 7` sum and
    `countSemi 5 2` would otherwise elaborate its index at `ZMod 7` — defeq, but simp
    matches syntactically.
Log lemmas restricted to the four whose shapes are already confirmed to compile:
`Real.logb_mul`, `Real.logb_pow`, `Real.logb_inv`, `Real.logb_self_eq_one` (ONE argument).
-/
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_LabelEntropyDeficit

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset LabelEntropy CyclicCubic in
/-- **The target, verbatim.** -/
theorem solution : MI pSemi = Real.logb 2 3 - 10 / 9 := by
  -- ---------- logarithm values ----------
  have h9 : Real.logb 2 (9:ℝ) = 2 * Real.logb 2 3 := by
    rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num]
    simp [Real.logb, Real.log_pow]
    ring
  have h18 : Real.logb 2 (18:ℝ) = 2 * Real.logb 2 3 + 1 := by
    rw [show (18:ℝ) = 2 * 3 ^ (2:ℕ) by norm_num]
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
    ring
  have h6 : Real.logb 2 (6:ℝ) = 1 + Real.logb 2 3 := by
    rw [show (6:ℝ) = 2 * 3 by norm_num,
        Real.logb_mul (by norm_num) (by norm_num),
        Real.logb_self_eq_one (by norm_num)]
  have h49 : Real.logb 2 ((4:ℝ)/9) = 2 - 2 * Real.logb 2 3 := by
    rw [show (4:ℝ)/9 = (2/3) ^ (2:ℕ) by norm_num, Real.logb_pow,
        show (2:ℝ)/3 = 2 * 3⁻¹ by norm_num,
        Real.logb_mul (by norm_num) (by norm_num), Real.logb_inv,
        Real.logb_self_eq_one (by norm_num)]
    ring
  -- ---------- the nlp terms, in the shapes norm_num actually leaves ----------
  have e6 : -((1:ℝ)/6 * Real.logb 2 (1/6)) = (1/6) * (1 + Real.logb 2 3) := by
    rw [one_div (6:ℝ), Real.logb_inv, ← h6]; ring
  have e19 : -((1:ℝ)/9 * Real.logb 2 (1/9)) = (1/9) * (2 * Real.logb 2 3) := by
    rw [one_div (9:ℝ), Real.logb_inv, ← h9]; ring
  have e18 : -((1:ℝ)/18 * Real.logb 2 (1/18)) = (1/18) * (2 * Real.logb 2 3 + 1) := by
    rw [one_div (18:ℝ), Real.logb_inv, ← h18]; ring
  have e49 : -((4:ℝ)/9 * Real.logb 2 (4/9)) = (4/9) * (2 * Real.logb 2 3 - 2) := by
    rw [h49]; ring
  -- ---------- the 21 cell counts (Fin 7 indices, see header) ----------
  have c00 : countSemi (0 : Fin 7) 0 = 0 := by decide
  have c01 : countSemi (0 : Fin 7) 1 = 0 := by decide
  have c02 : countSemi (0 : Fin 7) 2 = 0 := by decide
  have c10 : countSemi (1 : Fin 7) 0 = 4 := by decide
  have c11 : countSemi (1 : Fin 7) 1 = 0 := by decide
  have c12 : countSemi (1 : Fin 7) 2 = 2 := by decide
  have c20 : countSemi (2 : Fin 7) 0 = 2 := by decide
  have c21 : countSemi (2 : Fin 7) 1 = 4 := by decide
  have c22 : countSemi (2 : Fin 7) 2 = 0 := by decide
  have c30 : countSemi (3 : Fin 7) 0 = 2 := by decide
  have c31 : countSemi (3 : Fin 7) 1 = 4 := by decide
  have c32 : countSemi (3 : Fin 7) 2 = 0 := by decide
  have c40 : countSemi (4 : Fin 7) 0 = 2 := by decide
  have c41 : countSemi (4 : Fin 7) 1 = 4 := by decide
  have c42 : countSemi (4 : Fin 7) 2 = 0 := by decide
  have c50 : countSemi (5 : Fin 7) 0 = 2 := by decide
  have c51 : countSemi (5 : Fin 7) 1 = 4 := by decide
  have c52 : countSemi (5 : Fin 7) 2 = 0 := by decide
  have c60 : countSemi (6 : Fin 7) 0 = 4 := by decide
  have c61 : countSemi (6 : Fin 7) 1 = 0 := by decide
  have c62 : countSemi (6 : Fin 7) 2 = 2 := by decide
  -- ---------- H of the marginal over k ----------
  have hA : H Finset.univ (fun a : ZMod 7 => ∑ b : Fin 3, pSemi (a, b))
      = 1 + Real.logb 2 3 := by
    show (∑ n : Fin 7, nlp (∑ k : Fin 3, pSemi (n, k))) = _
    simp only [Fin.sum_univ_seven, Fin.sum_univ_three]
    simp only [pSemi, nlp, c00, c01, c02, c10, c11, c12, c20, c21, c22,
               c30, c31, c32, c40, c41, c42, c50, c51, c52, c60, c61, c62]
    norm_num
    simp only [e6]
    ring
  -- ---------- H of the marginal over n ----------
  have m0 : (∑ a : ZMod 7, pSemi (a, (0 : Fin 3))) = 4/9 := by
    show (∑ n : Fin 7, pSemi (n, (0 : Fin 3))) = _
    simp only [Fin.sum_univ_seven]
    simp only [pSemi, c00, c10, c20, c30, c40, c50, c60]
    norm_num
  have m1 : (∑ a : ZMod 7, pSemi (a, (1 : Fin 3))) = 4/9 := by
    show (∑ n : Fin 7, pSemi (n, (1 : Fin 3))) = _
    simp only [Fin.sum_univ_seven]
    simp only [pSemi, c01, c11, c21, c31, c41, c51, c61]
    norm_num
  have m2 : (∑ a : ZMod 7, pSemi (a, (2 : Fin 3))) = 1/9 := by
    show (∑ n : Fin 7, pSemi (n, (2 : Fin 3))) = _
    simp only [Fin.sum_univ_seven]
    simp only [pSemi, c02, c12, c22, c32, c42, c52, c62]
    norm_num
  have hB : H Finset.univ (fun b : Fin 3 => ∑ a : ZMod 7, pSemi (a, b))
      = 2 * Real.logb 2 3 - 16/9 := by
    show (∑ k : Fin 3, nlp (∑ a : ZMod 7, pSemi (a, k))) = _
    simp only [Fin.sum_univ_three, m0, m1, m2, nlp]
    norm_num
    simp only [e49, e19]
    ring
  -- ---------- H of the joint (this is target 30c0c5bc) ----------
  have hJ : H Finset.univ pSemi = 2 * Real.logb 2 3 + 1 / 3 := by
    show (∑ q : ZMod 7 × Fin 3, nlp (pSemi q)) = _
    rw [Fintype.sum_prod_type]
    show (∑ n : Fin 7, ∑ k : Fin 3, nlp (pSemi (n, k))) = _
    simp only [Fin.sum_univ_seven, Fin.sum_univ_three]
    simp only [pSemi, nlp, c00, c01, c02, c10, c11, c12, c20, c21, c22,
               c30, c31, c32, c40, c41, c42, c50, c51, c52, c60, c61, c62]
    norm_num
    simp only [e19, e18]
    ring
  -- ---------- assemble ----------
  unfold MI
  rw [hA, hB, hJ]
  ring
