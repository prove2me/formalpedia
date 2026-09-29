-- Prove2me | Theorems.Thm_mme_dwz_square_repaired_standard_family_exact_hash_loss
-- name    : mme_dwz_square_repaired_standard_family_exact_hash_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:15:13.841161+00:00
-- url     : https://prove2.me/theorems/141cf71d-528f-45fd-a6aa-983ccb66ecc9
-- title:
--   Equation (24): repaired Table-2 family with the exact finite hash loss
-- statement:
--   Put $L=10^{16}m$ and $B=32\cdot6^{20}\cdot70!$. For every sufficiently large $m$, there are a common hashing modulus $p\ge2$, a positive finite denominator $D$, and $k$ repaired literal Table-2 standard copies such that
--
--   $$
--   p\le e^{16(L+1)},\qquad D\le e^{B\sqrt{L+1}},
--   $$
--
--   the source tensor $(CW_6\otimes CW_6)^{\otimes L}$ restricts to their direct sum, and
--
--   $$
--   2^{L_{\rm ret}L}
--   \frac{\lfloor p/2\rfloor}{p}
--   \frac{e^{-4\sqrt{\log\lfloor p/2\rfloor}}}{D}
--   \le k.
--   $$
--
--   This is the exact finite source-and-hashing form of Equation (24). It retains the integer half-modulus factor, the explicit Behrend density, and the full polynomial denominator. A separate analytic theorem absorbs precisely these displayed factors into one $e^{-C\sqrt{L+1}}$ loss.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173v5, Additional Zeroing-Out Steps 1--4, Corollary 5.11, Claim 6.8, and Equation (24), printed pp. 48--58; the displayed finite Behrend factor is from Section 3.10, printed pp. 24--26.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_CW_tensor

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_square_repaired_standard_family_exact_hash_loss
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      let L : ℕ := MME.DWZTable2Counts.scale * m
      let B : ℝ := 32 * 6 ^ 20 * ((70 : ℕ).factorial : ℝ)
      ∃ (k p : ℕ) (D : ℝ),
        2 ≤ p ∧
        (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) ∧
        0 < D ∧
        D ≤ Real.exp (B * Real.sqrt (((L + 1 : ℕ) : ℝ))) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun _ : Fin k => dwzTable2StandardObj K m))
          ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L) ∧
        Real.rpow 2 (retainedLogRate * (L : ℝ)) *
            (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
                Real.exp
                  (-4 * Real.sqrt
                    (Real.log (((p / 2 : ℕ) : ℝ))))) /
              D) ≤
          (k : ℝ) := by
  sorry
