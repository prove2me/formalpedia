-- Prove2me | Theorems.Thm_mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
-- name    : mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:21:32.482695+00:00
-- url     : https://prove2.me/theorems/07cc7a31-a24d-44ad-92be-e2b2027088c2
-- title:
--   Cofinal finite CW square extractions strictly below the 2.376 rate
-- statement:
--   Fix $q=6$, $3\tau\ge2$, and the exact rational joint profile of the Coppersmith--Winograd $2.376$ certificate. Assume that every nonnegative cyclic coupled base strictly below
--
--   $$
--   C(\tau)=4\,6^{3\tau}(6^{3\tau}+2)
--   $$
--
--   has a concrete tau-value witness. For every nonnegative target base
--
--   $$
--   V<\operatorname{auxiliaryRHS}(6,\tau,a,b,c,d),
--   $$
--
--   there is a fixed coupled base $0\le V_c<C(\tau)$ that is attained, together with cofinal integer scales $m_n\to\infty$. At every sufficiently large selected scale, the joint orbit multiplicities are exactly
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
--   and a concrete direct sum of matrix-multiplication tensors restricts from $T_6^{\otimes6{,}000{,}000m_n}$ with tau-weight at least
--
--   $$
--   V^{3{,}000{,}000m_n}.
--   $$
--
--   The strict gaps $V_c<C(\tau)$ and $V<\operatorname{auxiliaryRHS}$ absorb the Stirling and Salem--Spencer factors $\exp(-o(N))$. Thus the theorem records the paper's actual exponential-rate conclusion while retaining the exact finite profile and the literal tensor restriction at every selected power.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square extraction, equations (11)--(13), Stirling estimates, Salem--Spencer pruning, and auxiliary inequality on journal pp. 265--269 (PDF pp. 15--19), together with the coupled lemma on journal pp. 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_2376_cofinal_extraction_below_of_coupled_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      ∀ Vc : ℝ, 0 ≤ Vc →
        Vc <
          4 * (6 : ℝ) ^ (3 * tau) *
            ((6 : ℝ) ^ (3 * tau) + 2) →
        HasTauValueAtLeast
          (cyclicSymmetrization (coupledObj K 6)) tau Vc)
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    (hV_lt :
      V < auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) :
    ∃ Vc : ℝ,
      0 ≤ Vc ∧
      Vc <
        4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2) ∧
      HasTauValueAtLeast
        (cyclicSymmetrization (coupledObj K 6)) tau Vc ∧
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
