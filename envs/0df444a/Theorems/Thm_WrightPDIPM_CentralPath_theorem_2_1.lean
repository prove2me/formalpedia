-- Prove2me | Theorems.Thm_WrightPDIPM_CentralPath_theorem_2_1
-- name    : WrightPDIPM.CentralPath.theorem_2_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:46.21622+00:00
-- url     : https://prove2.me/theorems/19e15675-3249-4c1f-b120-bca79de1d383
-- title:
--   Theorem 2.1 — F ≠ ∅ implies Ω ≠ ∅; one LP has a solution iff the other does, with equal values
-- statement:
--   Consider the standard-form primal (2.1) $\min c^{\mathsf T}x$ s.t. $Ax = b$, $x \ge 0$ and its dual (2.2) $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$, with $A \in \mathbb{R}^{m\times n}$ arbitrary. Let $\mathcal F$ be the primal-dual feasible set, $\Omega_P$ and $\Omega_D$ the primal and dual solution sets, and $\Omega = \Omega_P \times \Omega_D$.
--
--   1. If the primal and dual are both feasible, the primal-dual solution set is nonempty:
--   $$\mathcal F \ne \emptyset \;\Longrightarrow\; \Omega \neq \emptyset .$$
--   2. If either problem has an optimal solution, so does the other, and the optimal objective values are equal:
--   $$\Omega_P \ne \emptyset \ \text{or}\ \Omega_D \neq \emptyset \;\Longrightarrow\; \Omega_P \ne\emptyset,\ \Omega_D \ne \emptyset,\ \text{and } c^{\mathsf T}x^* = b^{\mathsf T}\lambda^* \text{ for all } x^* \in \Omega_P,\ (\lambda^*, s^*) \in \Omega_D .$$
--
--   This is the existence and strong-duality statement for standard-form linear programming on which the rest of the chapter builds.
--
--   **Formalization Note** "The objective values are equal" is stated for every pair of optimal solutions, which is what equality of the two optimal values means. No rank assumption on $A$.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 25, Theorem 2.1

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace WrightPDIPM.CentralPath

open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 25, Theorem 2.1.
(i) If `F ≠ ∅`, the primal-dual solution set `Ω` is nonempty.
(ii) If either (2.1) or (2.2) has an optimal solution, so does the other, and the objective
values are equal (`cᵀx* = bᵀλ*` for every `x* ∈ Ω_P`, `(λ*, s*) ∈ Ω_D`). -/
theorem theorem_2_1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    ((F A b c).Nonempty → (Omega A b c).Nonempty) ∧
    ((OmegaP A b c).Nonempty ∨ (OmegaD A b c).Nonempty →
      (OmegaP A b c).Nonempty ∧ (OmegaD A b c).Nonempty ∧
        ∀ x ∈ OmegaP A b c, ∀ p ∈ OmegaD A b c, c ⬝ᵥ x = b ⬝ᵥ p.1) := by sorry

end WrightPDIPM.CentralPath
