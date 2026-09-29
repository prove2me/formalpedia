-- Prove2me | Theorems.Thm_mme_dwz_q5_full_ambient_degree_entropy_bound
-- name    : mme_dwz_q5_full_ambient_degree_entropy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T13:57:27.237346+00:00
-- url     : https://prove2.me/theorems/ab71e85e-f03d-433a-80dd-87f6e2cdaa14
-- title:
--   Full ambient degree entropy bounds for the exact q=5 fourth-power family
-- statement:
--   Use the unchanged rational $q=5$ fourth-power data and the synchronized integer counts from the global asymptotic data definition. Let $C=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}$, so $|C|=45$. For an integer $t>0$, write $N=N(t)$ and let $M_{a,g}(t)$ be the prescribed marginal counts in mode $a\in\{0,1,2\}$. Let $\mathcal T_t$ contain every nonnegative integer joint table $h:C\to\{0,\ldots,N\}$ having all three prescribed marginals. Define the full ambient mode-star count by
--   $$
--   D_a(t)=\sum_{h\in\mathcal T_t}
--   \prod_{g=0}^{8}\frac{M_{a,g}(t)!}{\prod_{c\in C:c_a=g}h(c)!}.
--   $$
--   The quotients are exact integer row multinomials. Put
--   $$
--   H_a=\sum_{g=0}^{8}-A_{a,g}\log A_{a,g},
--   \qquad A_{a,g}=\frac{\operatorname{marginal}(a,g)}{2\cdot10^{15}},
--   \qquad
--   U=\frac{2830114015881672025944380699373}{10^{30}},
--   $$
--   with $0\log0=0$ and natural logarithms. Then, simultaneously for every mode,
--   $$
--   D_a(t)\le (N(t)+1)^{45}\exp\!\bigl(N(t)(U-H_a)\bigr).
--   $$
--   The upper entropy bound is derived from the already proved certificate for all real distributions with these marginals; it is not an assumption on the optimizing joint table. Consequently the estimate controls the complete ambient family, including joint types different from the selected target type. No asymptotic compatibility bound, prime choice, tensor value estimate, or matrix-multiplication exponent is asserted here.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Sections 3.10 and 6.2 and Remark 4.3. Derived full-marginal-family type-count estimate for the original q=5 rational data, using proved global entropy ceiling mme_dwz_fourth_global_entropy_upper (63664deb-855a-4e5a-9723-a0de29647ace), the exact q=5 profile certificate, and dependent-row entropy bounds.

import Definitions.Def_mme_dwz_q5_global_asymptotic_data

open MME.DWZQ5AsymptoticData MME.DWZFourthGlobalWitness
set_option autoImplicit false

theorem mme_dwz_q5_full_ambient_degree_entropy_bound (t : ℕ) (ht : 0 < t) (mode : Fin 3) :
    (degree t mode : ℝ) ≤ ((N t : ℝ) + 1) ^ 45 *
      Real.exp ((N t : ℝ) * ((entropyUpper : ℝ) - marginalEntropy mode)) := by sorry
