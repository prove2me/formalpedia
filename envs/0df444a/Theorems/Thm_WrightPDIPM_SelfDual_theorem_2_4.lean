-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_2_4
-- name    : WrightPDIPM.SelfDual.theorem_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:12.745959+00:00
-- url     : https://prove2.me/theorems/ca448993-0606-4870-8832-136103ac453b
-- title:
--   Theorem 2.4 (Goldman–Tucker) — B ∪ N = {1, …, n}: the LP pair has a strictly complementary solution when Ω ≠ ∅
-- statement:
--   Let $A \in \mathbb R^{m\times n}$, $b \in \mathbb R^m$, $c \in \mathbb R^n$ and consider the pair (9.3a) $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and (9.3b) $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$, with solution sets $\Omega_P$, $\Omega_D$ and $\Omega = \Omega_P \times \Omega_D$. Let $\mathcal B = \{j : x^*_j \ne 0$ for some $x^* \in \Omega_P\}$ and $\mathcal N = \{j : s^*_j \ne 0$ for some $(\lambda^*, s^*) \in \Omega_D\}$. If $\Omega \ne \emptyset$, then
--   $$\mathcal B \cup \mathcal N = \{1, 2, \dots, n\},$$
--   and there exist $x^* \in \Omega_P$ and $(\lambda^*, s^*) \in \Omega_D$ with $x^* + s^* > 0$.
--
--   This is the Goldman–Tucker theorem: every solvable LP pair has a strictly complementary primal-dual solution. Chapter 9 uses it to show that a solvable LP produces a strictly complementary solution of the simplified HSD mLCP with $\tau^* > 0$.
--
--   **Formalization Note** The page states the theorem without hypothesis; its section (p. 27, "For every solution $(x^*, \lambda^*, s^*)$") presupposes that solutions exist, and the statement is false for an LP pair without solutions. The standing hypothesis $\Omega \ne \emptyset$ is therefore explicit. Both sentences of the theorem are stated. This restates, inside this mission's namespace, the Chapter 2 result, because drafts cannot import another draft's definitions.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 28, Theorem 2.4

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem 2.4 (Goldman–Tucker) (p. 28), for the pair (9.3) = (2.1)/(2.2):
`B ∪ N = {1, …, n}`; that is, there exist `x* ∈ Ω_P` and `(λ*, s*) ∈ Ω_D` with `x* + s* > 0`.
Both sentences are stated. The standing case of the section (p. 27: "For every solution
(x*, λ*, s*)"), `Ω ≠ ∅`, is carried as `hΩ`. -/
theorem theorem_2_4 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hΩ : (Omega A b c).Nonempty) :
    indexB A b c ∪ indexN A b c = Set.univ ∧
    ∃ x ∈ OmegaP A b c, ∃ p ∈ OmegaD A b c, ∀ j, 0 < x j + p.2 j := by sorry

end WrightPDIPM.SelfDual
