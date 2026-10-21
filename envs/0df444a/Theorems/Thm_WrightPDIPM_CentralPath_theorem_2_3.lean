-- Prove2me | Theorems.Thm_WrightPDIPM_CentralPath_theorem_2_3
-- name    : WrightPDIPM.CentralPath.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:54.047137+00:00
-- url     : https://prove2.me/theorems/fac0d8bf-c29c-4026-8f95-f1364c985fd0
-- title:
--   Theorem 2.3 — strict dual feasibility bounds Ω_P; strict primal feasibility bounds the dual slacks
-- statement:
--   Consider the standard-form primal (2.1) $\min c^{\mathsf T}x$ s.t. $Ax=b$, $x\ge 0$ and dual (2.2) $\max b^{\mathsf T}\lambda$ s.t. $A^{\mathsf T}\lambda + s = c$, $s \ge 0$, with $A \in \mathbb{R}^{m \times n}$ arbitrary, and suppose both are feasible, $\mathcal F \ne \emptyset$. A pair $(\lambda, s)$ is strictly dual feasible if $A^{\mathsf T}\lambda + s = c$, $s > 0$; a vector $x$ is strictly primal feasible if $Ax = b$, $x > 0$. Then
--
--   1. if the dual has a strictly feasible point, the primal solution set $\Omega_P$ is nonempty and bounded;
--   2. if the primal has a strictly feasible point, the set
--   $$\{ s^* \mid (\lambda^*, s^*) \in \Omega_D \text{ for some } \lambda^* \in \mathbb{R}^m \}$$
--   is nonempty and bounded.
--
--   The two halves have separate hypotheses. They explain why interior-point methods need strictly feasible points: strict feasibility on one side keeps the solutions of the other side in a bounded region.
--
--   **Formalization Note** "Bounded" is `Bornology.IsBounded` in $\mathbb{R}^n$ (any norm). The common hypothesis $\mathcal F \neq \emptyset$ is shared, each strict-feasibility hypothesis governs only its own conclusion.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 26, Theorem 2.3

import Mathlib
import Definitions.Def_WrightPDIPM_CentralPath_LP

namespace WrightPDIPM.CentralPath

open Matrix

/-- Wright, *Primal-Dual Interior-Point Methods*, SIAM 1997, p. 26, Theorem 2.3. Suppose
`F ≠ ∅`. If the dual has a strictly feasible point, `Ω_P` is nonempty and bounded; if the
primal has a strictly feasible point, `{s* | (λ*, s*) ∈ Ω_D for some λ*}` is nonempty and
bounded. The two halves carry separate hypotheses. -/
theorem theorem_2_3 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (hF : (F A b c).Nonempty) :
    ((∃ lam s, StrictlyDualFeasible A c lam s) →
      (OmegaP A b c).Nonempty ∧ Bornology.IsBounded (OmegaP A b c)) ∧
    ((∃ x, StrictlyPrimalFeasible A b x) →
      {s : Fin n → ℝ | ∃ lam, (lam, s) ∈ OmegaD A b c}.Nonempty ∧
        Bornology.IsBounded {s : Fin n → ℝ | ∃ lam, (lam, s) ∈ OmegaD A b c}) := by sorry

end WrightPDIPM.CentralPath
