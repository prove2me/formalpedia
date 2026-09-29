-- Prove2me | Theorems.Thm_mme_recursive_assembly_of_numerical_repair_budgets
-- name    : mme_recursive_assembly_of_numerical_repair_budgets
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T09:38:21.304493+00:00
-- url     : https://prove2.me/theorems/88fb54c2-24fa-49ed-bd5d-b60686eae1f3
-- title:
--   Recursive assembly from numerical repair budgets
-- statement:
--   Let $K$ be a field, $D$ finite hash-extraction data, and $A_j$ a recursive Y/Z stage for each factor $j$. Write $T_j$ for its intact template, $r_j=8^{e_j}$ for its repair group size, $\lambda_j$ for the hash lower bound, and $R$ for the global repair divisor. Assume raw-source compatibility and local restrictions $\langle a_j,b_j,c_j\rangle\preceq T_j$, where the products of the three local dimensions equal the global dimensions $(a,b,c)$. Suppose
--
--   $$
--   \lambda_j\ge r_j\quad\text{for every }j,
--   \qquad R\ge\prod_j(2r_j).
--   $$
--
--   Then the stages satisfy recursive assembly. In particular, for every integer count family $n_j\ge\lambda_j$,
--
--   $$
--   \bigoplus_{1\le s\le\lfloor\prod_jn_j/R\rfloor}\langle a,b,c\rangle
--   \preceq
--   \bigotimes_j\left(\bigoplus_{1\le t\le\lfloor n_j/r_j\rfloor}T_j\right).
--   $$
--
--   Here $X\preceq Y$ means that $X$ is a restriction of $Y$. This gives a numerical sufficient condition for the copy-count part of recursive assembly, with matrix tensors extracted from the templates in the required direction.
-- source:
--   The forward-field recursive assembly theorem, finite repaired matrix-product copy budgets, and recursive Y/Z finite assembly certificate in this environment.

import Theorems.Thm_mme_more_asymmetry_recursive_assembly_from_forward_fields
import Theorems.Thm_mme_finite_repaired_MM_product_from_copy_budgets
import Theorems.Thm_mme_recursive_yz_certificate_finite_assembly

open BigOperators MME MME.RecursiveYZ.Certificate
universe u

theorem mme_recursive_assembly_of_numerical_repair_budgets {K : Type u} [Field K]
    (D : HashExtraction.Data) (A : ∀ j, Stage (D.hash j))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (a b c : Fin D.factors → ℕ)
    (htemplate : ∀ j, TensorObj.Restrict (MMObj K (a j) (b j) (c j)) ((A j).template K))
    (ha : (∏ j, a j) = D.a) (hb : (∏ j, b j) = D.b) (hc : (∏ j, c j) = D.c)
    (hlower : ∀ j, ((8 ^ (A j).repairExponent : ℕ) : ℝ) ≤ (D.hash j).lower)
    (hrepair : (∏ j, 2 * 8 ^ (A j).repairExponent) ≤ D.repairCopies) :
    RecursiveAssembly D A K := by sorry
