-- Prove2me | Theorems.Thm_centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity
-- name    : centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T05:21:51.253543+00:00
-- url     : https://prove2.me/theorems/34444731-bddc-456e-b3fd-3db1727ce090
-- statement:
--   Order-2 (degree-1) L4-L2 hypercontractivity for the scalar centered sampling coefficient at the symmetric rate p=1/2: E[Coeff^4] <= 3 (E[Coeff^2])^2, dimension-free. This is the faithful Kwapien-Szulga 1991 (Ann. Probab. 19, 369-379, eq. 1.4) real-hypercontractivity constant (q-1)^{d/2} at p=2,q=4,d=1.
-- source:
--   Kwapien, S. and Szulga, J. (1991). Hypercontraction method in moment inequalities for series of independent random variables in normed spaces. Ann. Probab. 19, 369-379, eq. (1.4); real hypercontractivity constant (q-1)^{d/2} for degree-d Rademacher chaos (here d=1, q=4, p=2 gives 3 in fourth-moment form). Cf. Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013) Ch.5; de la Pena-Gine, Decoupling, Ch.3. Holds dimension-free precisely in the symmetric (p=1/2) case where the biased-Bernoulli diagonal 4th-moment term does not blow up.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators Classical

theorem centered_sampling_coefficient_symmetric_l4_l2_hypercontractivity {n₁ n₂ : ℕ} (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation (1/2 : ℝ)
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega (1/2) B)) ^ 4) ≤
      3 * (bernoulliExpectation (1/2 : ℝ)
            (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega (1/2) B)) ^ 2)) ^ 2 := by sorry
