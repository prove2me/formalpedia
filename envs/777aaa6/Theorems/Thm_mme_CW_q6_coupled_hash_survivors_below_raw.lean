-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_hash_survivors_below_raw
-- name    : mme_CW_q6_coupled_hash_survivors_below_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:34:11.522299+00:00
-- url     : https://prove2.me/theorems/f676593d-2b82-4025-aa22-d84ca911c4cd
-- title:
--   Salem--Spencer hashing produces enough mode-disjoint coupled survivors
-- statement:
--   Fix $\tau$ with $3\tau\ge2$ and a nonnegative $V$ strictly below the raw limiting base $4\,6^{3\tau}(6^{3\tau}+2)$. For sufficiently large $N$, use the exact type counts
--
--   $$
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad G=N-L,
--   $$
--
--   and assume the pruning certificate $L>0$, $L+G=N$, and $341L<100G$. Then Salem--Spencer hashing and collision pruning produce $k$ pairwise mode-disjoint copies of the fine-structure survivor $S_{L,G}$, giving a concrete restriction
--
--   $$
--   \bigoplus_{j<k}S_{L,G}\;\leq_{\mathrm{Restrict}}\;\operatorname{cyc}(D_6)^{\otimes2N}.
--   $$
--
--   Writing $s=36^{2G}6^{2L}=6^{4G+2L}$ for the square side obtained from each survivor, their count is large enough that
--
--   $$
--   V^{2N}\le k\,(s^3)^{\tau}.
--   $$
--
--   This is exactly the finite combinatorial boundary on CW90 journal pp. 270--271: the dense 3AP-free set prevents hash collisions, shared mode blocks are pruned, and the strict gap below the limiting base absorbs both Salem--Spencer and Stirling subexponential losses. The theorem deliberately stops before converting each survivor into a matrix-multiplication tensor.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled-constituent proof on journal pp. 270--271 (PDF pp. 20--21): the 2N-th power, modulus M, Salem--Spencer set B, hash equality, shared-X/Y pruning, disjoint C-tensor objects, and finite value estimate; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_q6_coupled_survivor
import Theorems.Thm_mme_salem_spencer_eps_form
import Theorems.Thm_mme_3AP_free_no_collision
open MME BigOperators Filter
universe u

theorem mme_CW_q6_coupled_hash_survivors_below_raw
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ k : ℕ,
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin k => coupledQ6Survivor K L G))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          (k : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by sorry
