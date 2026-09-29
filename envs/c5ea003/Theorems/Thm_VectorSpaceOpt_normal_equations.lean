-- Prove2me | Theorems.Thm_VectorSpaceOpt_normal_equations
-- name    : VectorSpaceOpt.normal_equations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:23:50.449517+00:00
-- url     : https://prove2.me/theorems/90c49c2b-ddb6-486f-9920-cc4cf2d94528
-- title:
--   The normal equations characterize the best approximation
-- statement:
--   Let $y_1, \dots, y_n$ be vectors in a real inner product space $H$, generating the subspace $M = \operatorname{span}\{y_1, \dots, y_n\}$, and let $x \in H$. We seek the vector of $M$ closest to $x$, written in coordinates as $\hat{x} = \alpha_1 y_1 + \cdots + \alpha_n y_n$.
--
--   The theorem says that the coefficients $\alpha_1, \dots, \alpha_n$ make $\hat x$ a best approximation to $x$ from $M$ **if and only if** they satisfy the **normal equations**:
--
--   $$\langle y_1, y_i\rangle\, \alpha_1 + \langle y_2, y_i\rangle\, \alpha_2 + \cdots + \langle y_n, y_i\rangle\, \alpha_n = \langle x,\, y_i\rangle, \qquad i = 1, \dots, n.$$
--
--   These are exactly the conditions that the error $x - \hat x$ be orthogonal to each $y_i$, so the equivalence is the projection theorem's orthogonality criterion written in coordinates. The coefficient matrix is the Gram matrix of the $y_i$.
--
--   Linear independence of the $y_i$ is **not** required for this equivalence — it governs whether the solution is unique, not whether a solution is optimal. When the $y_i$ are dependent the system is still consistent, but its solutions form a multiplicity.
--
--   **Formalization Note.** The claim is an equivalence for a given coefficient family, and asserts nothing about the existence of a solution; the minimality side is stated as an explicit norm inequality against every element of the span, not through a projection operator.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.6, the normal equations, pp. 55–56

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem normal_equations {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (y : Fin n → H) (x : H) (α : Fin n → ℝ) :
    (∀ i, ∑ j, ⟪y j, y i⟫ * α j = ⟪x, y i⟫) ↔
    (∀ m ∈ Submodule.span ℝ (Set.range y), ‖x - ∑ j, α j • y j‖ ≤ ‖x - m‖) := by sorry

end VectorSpaceOpt
