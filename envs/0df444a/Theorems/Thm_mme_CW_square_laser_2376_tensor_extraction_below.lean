-- Prove2me | Theorems.Thm_mme_CW_square_laser_2376_tensor_extraction_below
-- name    : mme_CW_square_laser_2376_tensor_extraction_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:29:50.487451+00:00
-- url     : https://prove2.me/theorems/67f1c3e1-8fd7-4813-b147-d5c343d56a12
-- title:
--   Exact-profile CW square hashing and assembly below a generalized coupled rate
-- statement:
--   Fix $q=6$, $3\tau\ge2$, and a nonnegative cyclic coupled base $V_c$ that is concretely attained. Let $V$ be a nonnegative number strictly below the generalized Section 8 profile base
--
--   $$
--   V<B_{V_c}(6,\tau,a,b,c,d)
--   $$
--
--   at the exact $2.376$ frequencies. Then there are cofinal scales $m_n\to\infty$ such that, for all sufficiently large $n$, the joint orbit multiplicities are exactly
--
--   $$
--   (699,37518,307638,616627)m_n,
--   $$
--
--   the five equation-(13) marginals are exactly
--
--   $$
--   (384072,1308290,1231903,75036,699)m_n,
--   $$
--
--   and an actual finite direct sum of matrix-multiplication tensors restricts from $T_6^{\otimes6{,}000{,}000m_n}$ with tau-weight at least
--
--   $$
--   V^{3{,}000{,}000m_n}.
--   $$
--
--   This is the tensor-only five-grade type-selection, Salem--Spencer hashing, collision elimination, coupled-block substitution, and Stirling assembly step. The strict inequality below $B_{V_c}$ absorbs every subexponential loss while the conclusion retains the literal finite restriction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square type selection, equations (11)--(13), Salem--Spencer pruning, coupled substitution, and auxiliary bound on journal pp. 265--269 (PDF pp. 15--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS_coupled
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_2376_tensor_extraction_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (hVc_value :
      HasTauValueAtLeast
        (cyclicSymmetrization (coupledObj K 6)) tau Vc)
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    (hV_lt :
      V < auxiliaryRHSWithCoupled 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d Vc) :
    ∃ m : ℕ → ℕ,
      Tendsto m atTop atTop ∧
      ∀ᶠ n : ℕ in atTop,
        (3 * (699 * m n) + 6 * (37518 * m n) +
            3 * (307638 * m n) + 3 * (616627 * m n) =
              3000000 * m n ∧
          2 * (699 * m n) + 2 * (37518 * m n) +
              307638 * m n = 384072 * m n ∧
          2 * (37518 * m n) + 2 * (616627 * m n) =
              1308290 * m n ∧
          2 * (307638 * m n) + 616627 * m n =
              1231903 * m n ∧
          2 * (37518 * m n) = 75036 * m n ∧
          699 * m n = 699 * m n ∧
          384072 * m n + 1308290 * m n + 1231903 * m n +
              75036 * m n + 699 * m n = 3000000 * m n) ∧
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
            ((CWObj K 6).kronPow (6000000 * m n)) ∧
          V ^ (3000000 * m n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by sorry
