-- Prove2me | Theorems.Thm_mme_CW_square_laser_2376_cofinal_extraction_of_coupled
-- name    : mme_CW_square_laser_2376_cofinal_extraction_of_coupled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T04:54:23.221611+00:00
-- url     : https://prove2.me/theorems/1cd2fe66-1c6a-45d5-96b3-c668a625aa16
-- title:
--   Cofinal finite CW square extractions at the exact 2.376 profile
-- statement:
--   Fix $q=6$ and the exact rational Section-8 frequencies used by the $2.376$ certificate. Assume the three coupled $(1,1,2)$ constituents jointly have the symmetric tau-value from the coupled-piece lemma. Then there are cofinal integer scales $m_n$ and errors $e_n\to0$ such that, for all sufficiently large $n$, a concrete direct sum of matrix-multiplication tensors restricts from
--
--   $$
--   T_6^{\otimes 6{,}000{,}000m_n},
--   $$
--
--   and its tau-weight is at least
--
--   $$
--   \operatorname{auxiliaryRHS}(6,\tau,a,b,c,d)^{3{,}000{,}000m_n}(1-e_n).
--   $$
--
--   The exponents come from the exact integer profile: $3{,}000{,}000m_n$ square factors contain joint multiplicities $(699,37518,307638,616627)m_n$. A finite coupled witness at power $m_n$ is Kronecker-powered $616627$ times to synchronize the coupled orbit without assuming that an arbitrary frequent set meets a fixed residue class. The conclusion retains the full finite restriction required by the tau-value definition.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square extraction, equations (11)--(13), and auxiliary bound on journal pp. 265--269 (PDF pp. 15--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_2376_cofinal_extraction_of_coupled
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K 6) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (6 : ℝ) ^ tau *
         (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    ∃ (m : ℕ → ℕ) (error : ℕ → ℝ),
      Tendsto m atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
            ((CWObj K 6).kronPow (6000000 * m n)) ∧
          (auxiliaryRHS 6 tau
              cw2376_a cw2376_b cw2376_c cw2376_d) ^ (3000000 * m n) *
              (1 - error n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by sorry
