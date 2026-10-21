-- Prove2me | Theorems.Thm_WrightPDIPM_CentralPath_theorem_2_4
-- name    : WrightPDIPM.CentralPath.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:50.906378+00:00
-- url     : https://prove2.me/theorems/65607b61-a383-4fab-86bd-0ee7f9c6e7e0
-- title:
--   Theorem 2.4 (Goldman–Tucker) — B ∪ N = {1, …, n}: a strictly complementary solution exists
-- statement:
--   Consider the standard-form primal (2.1) $\min c^{\mathsf T}x$ s.t. $Ax=b$, $x\ge 0$ and dual (2.2) $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$, with $A\in\mathbb{R}^{m\times n}$ arbitrary, and suppose both are feasible, $\mathcal F \neq \emptyset$. Let $\Omega_P$, $\Omega_D$ be the solution sets and
--   $$\mathcal B = \{j \mid x^*_j \ne 0 \text{ for some } x^* \in \Omega_P\}, \qquad \mathcal N = \{j \mid s^*_j \neq 0 \text{ for some } (\lambda^*, s^*) \in \Omega_D\}.$$
--   Then
--   $$\mathcal B \cup \mathcal N = \{1, 2, \dots, n\},$$
--   and, equivalently as the book puts it, there exist $x^* \in \Omega_P$ and $(\lambda^*, s^*) \in \Omega_D$ with $x^* + s^* > 0$ (componentwise).
--
--   Such a pair is a **strictly complementary** solution. Since $\mathcal B \cap \mathcal N = \emptyset$ by complementarity, the theorem says $\mathcal B, \mathcal N$ partition the index set; this partition drives the local and superlinear convergence analysis of primal-dual methods.
--
--   **Formalization Note** Both sentences of the theorem are stated, as a conjunction. The book prints Theorem 2.4 with no hypothesis; the section's standing case (both problems feasible, so $\Omega \ne \emptyset$ by Theorem 2.1, and the proof starts from a primal-dual solution) is carried explicitly as $\mathcal F \neq \emptyset$. Without it the statement is false (finding F1; see the sharpness probe `WrightPDIPM.CentralPath.theorem_2_4_probe`).
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 28, Theorem 2.4 (proof pp. 35–36); hypothesis F ≠ ∅ from the section's context, p. 27

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace WrightPDIPM.CentralPath

open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 28, Theorem 2.4
(Goldman–Tucker): `B ∪ N = {1, …, n}`; that is, there exist `x* ∈ Ω_P` and
`(λ*, s*) ∈ Ω_D` with `x* + s* > 0`. Both sentences are stated. The page prints no
hypothesis; the standing case of the section (`F ≠ ∅`, so `Ω ≠ ∅` by Theorem 2.1) is carried
as `hF` (FINDINGS.yaml F1: the statement is false without it). -/
theorem theorem_2_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hF : (F A b c).Nonempty) :
    indexB A b c ∪ indexN A b c = Set.univ ∧
    ∃ x ∈ OmegaP A b c, ∃ p ∈ OmegaD A b c, ∀ j, 0 < x j + p.2 j := by sorry

end WrightPDIPM.CentralPath
