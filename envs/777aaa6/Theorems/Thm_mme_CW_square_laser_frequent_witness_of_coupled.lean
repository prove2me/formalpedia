-- Prove2me | Theorems.Thm_mme_CW_square_laser_frequent_witness_of_coupled
-- name    : mme_CW_square_laser_frequent_witness_of_coupled
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T04:43:17.977906+00:00
-- url     : https://prove2.me/theorems/e96a1709-4145-47f2-a8ac-b2c53075335a
-- title:
--   Finite CW tensor-square laser witnesses from the coupled constituent
-- statement:
--   Let $q\ge3$, $3\tau\ge2$, and let $a,b,c,d>0$ satisfy $3a+6b+3c+3d=1$. Assume the coupled four-sum constituent has the symmetric tau-value established on journal pp. 270--272. Then, for every $\varepsilon>0$ and arbitrarily large $N$, there are finitely many concrete matrix-multiplication tensors $\langle x_i,y_i,z_i\rangle$ whose direct sum is a restriction of $(T_q\otimes T_q)^{\otimes N}$ and whose weighted volumes satisfy
--
--   $$
--   \operatorname{auxiliaryRHS}(q,\tau,a,b,c,d)^N(1-\varepsilon)\le \sum_i(x_i y_i z_i)^\tau.
--   $$
--
--   This is the finite-output form of the tensor-square type selection, Salem--Spencer hashing, collision pruning, and coupled-block substitution on journal pp. 265--269. The conclusion retains the actual direct-sum restriction; it is the finite witness consumed by the asymptotic tau-value predicate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square block selection, equations (11)--(13), pruning, and auxiliary inequality on journal pp. 265--269 (PDF pp. 15--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_frequent_witness_of_coupled
    {K : Type u} [Field K]
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K q) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (q : ℝ) ^ tau *
         (((q : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    ∀ epsilon > (0 : ℝ), ∃ᶠ N : ℕ in atTop,
      ∃ (k : ℕ) (x y z : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
          ((TensorObj.kron (CWObj K q) (CWObj K q)).kronPow N) ∧
        (auxiliaryRHS q tau a b c d) ^ N * (1 - epsilon) ≤
          ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by sorry
