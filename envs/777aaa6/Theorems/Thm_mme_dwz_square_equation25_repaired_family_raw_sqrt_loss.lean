-- Prove2me | Theorems.Thm_mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
-- name    : mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:48:34.619601+00:00
-- url     : https://prove2.me/theorems/9a6a7eca-b87c-4bb6-be51-562ae81b5f73
-- title:
--   Equation (25): raw repaired-family extraction before the closed-rate substitution
-- statement:
--   Fix a field $K$ and $\tau\ge2/3$. Write $L=10^{16}m$, let $L_{\mathrm{ret}}$ be the exact retained-copy exponent from the two asymmetric hashes, and let $B_s(\tau)$ be the fifteen exact Table-2 component bases. There is a constant $C\ge0$ such that, for every sufficiently large $m$, the $L$-th power of the full six-symmetrization of the literal tensor $CW_6\otimes CW_6$ restricts to a finite direct sum of matrix-multiplication tensors and
--
--   $$
--   \left(2^{L_{\mathrm{ret}}L}\prod_{s=1}^{15}B_s(\tau)^{n_s(m)}\right)^6
--    e^{-C\sqrt{L+1}}
--   \le\sum_i(a_i b_i c_i)^\tau.
--   $$
--
--   Here $n_s(m)$ is the exact integral multiplicity of constituent $s$ obtained by scaling the printed Table-2 distribution by $m$. This is the finite tensor-construction frontier of Equation (25): it retains the actual source restriction, all repaired copies, and the six symmetric orientations. It stops immediately before substituting the separately proved identity that the parenthesized one-orientation factor equals $R_{\mathrm{sq}}(\tau)^L$.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173, Lemma 5.6, Corollary 5.11, Lemma 6.7, Claim 6.8, Equation (24), Equation (25), and Section 6.3/Table 2, printed pp. 48-59.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_square_equation25_repaired_family_raw_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow
                (MME.DWZTable2Counts.scale * m)) ∧
          (Real.rpow 2
                (retainedLogRate *
                  ((MME.DWZTable2Counts.scale * m : ℕ) : ℝ)) *
              (∏ s : Fin 15,
                (componentBase tau s) ^
                  (MME.DWZTable2Counts.component s * m))) ^ (6 : ℕ) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
