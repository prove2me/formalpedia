-- Prove2me | solution 1 for CyclicCubic.H_semi_joint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T04:11:33.242677+00:00
-- url     : https://prove2.me/submissions/b897b157-67a7-4a63-87a4-4fd35ffcede4

/-
# `CyclicCubic.H_semi_joint`
Target `30c0c5bc` (Open, not deprecated at draft time; re-read live immediately before submitting).

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

Enumerating the 36 ordered pairs of nonzero residues mod 7 by product `n` and split-count `k`:
    n=0:(0,0,0)  n=1:(4,0,2)  n=2:(2,4,0)  n=3:(2,4,0)
    n=4:(2,4,0)  n=5:(2,4,0)  n=6:(4,0,2)
so pSemi takes the value 4/36 = 1/9 in six cells, 2/36 = 1/18 in six cells, and 0 in nine. Hence
    H = 6·nlp(1/9) + 6·nlp(1/18) = (2/3)·log₂9 + (1/3)·log₂18
      = (2/3)(2L) + (1/3)(2L+1) = 2L + 1/3,  where L = log₂3.
Verified numerically before writing (agrees to 4.4e-16).

Two presentation traps, both found by tracing the real goal rather than guessing:
  1. `Fin.sum_univ_succ` and `Fin.sum_univ_seven` in the same `simp only` means `succ` wins and
     expands recursively, leaving indices as `Fin.succ` towers instead of numerals. Use the
     arity-specific lemmas ALONE (`Fin.sum_univ_seven`, `Fin.sum_univ_three`).
  2. The sum is over `ZMod 7`, but the `show` retypes it, so the goal carries `Fin 7` numerals.
     `countSemi 5 2` elaborates `5 : ZMod 7` — defeq but not syntactically equal, so simp will
     not match. The hypotheses are therefore stated as `countSemi (5 : Fin 7) 2`; `decide`
     proves them either way.

TACTICS ARE PROBED, NOT GUESSED (see LESSONS): countSemi closes by `decide`; the product sum splits
by `Fintype.sum_prod_type`; `Fin 3` expands by `Fin.sum_univ_succ`; `ZMod 7` needs the explicit
`show (∑ n : Fin 7, ...)` before `Fin.sum_univ_seven`; and the logb identities are done by unfolding
`Real.logb` to `Real.log`, not via the named lemmas whose arities differ from what I first assumed.
-/
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Entropy
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_LabelEntropyDeficit

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Finset LabelEntropy CyclicCubic in
/-- **The target, verbatim.** -/
theorem solution : H Finset.univ pSemi = 2 * Real.logb 2 3 + 1 / 3 := by
  have h9 : Real.logb 2 (9:ℝ) = 2 * Real.logb 2 3 := by
    rw [show (9:ℝ) = 3 ^ (2:ℕ) by norm_num]
    simp [Real.logb, Real.log_pow]
    ring
  have h18 : Real.logb 2 (18:ℝ) = 2 * Real.logb 2 3 + 1 := by
    rw [show (18:ℝ) = 2 * 3 ^ (2:ℕ) by norm_num]
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow,
        Real.logb_self_eq_one (by norm_num)]
    ring
  -- goal shapes below were OBSERVED via trace_state, not assumed
  have e9 : -((1:ℝ)/9 * Real.logb 2 (1/9)) = (1/9) * (2 * Real.logb 2 3) := by
    rw [one_div (9:ℝ), Real.logb_inv, ← h9]; ring
  have e18 : -((1:ℝ)/18 * Real.logb 2 (1/18)) = (1/18) * (2 * Real.logb 2 3 + 1) := by
    rw [one_div (18:ℝ), Real.logb_inv, ← h18]; ring
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
  show (∑ q : ZMod 7 × Fin 3, nlp (pSemi q)) = _
  rw [Fintype.sum_prod_type]
  show (∑ n : Fin 7, ∑ k : Fin 3, nlp (pSemi (n, k))) = _
  simp only [Fin.sum_univ_seven, Fin.sum_univ_three]
  simp only [pSemi, nlp, c00, c01, c02, c10, c11, c12, c20, c21, c22,
             c30, c31, c32, c40, c41, c42, c50, c51, c52, c60, c61, c62]
  norm_num
  simp only [e9, e18]
  ring
