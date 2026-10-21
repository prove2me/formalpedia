-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_A_2
-- name    : WrightPDIPM.SelfDual.theorem_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:12.804222+00:00
-- url     : https://prove2.me/theorems/53198b53-d31b-46a8-b013-88257fad337e
-- title:
--   Theorem A.2 — for a convex program the KKT conditions are sufficient; strict convexity makes a local solution the unique global one
-- statement:
--   Consider problem (A.2), $\min f(u)$ subject to $Cu = d$, $Gu \ge h$, $u \in U$, and suppose it is a **convex programming problem**: $U \subset \mathbb R^N$ is open and convex and $f$ is convex on the feasible set $\{u \in U : Cu = d,\ Gu \ge h\}$.
--
--   1. If $u^* \in U$, $f$ is differentiable at $u^*$, and there are vectors $y, z$ such that
--   $$\nabla f(u^*) - C^{\mathsf T}y - G^{\mathsf T}z = 0,\quad Cu^* = d,\quad Gu^* \ge h,\quad z \ge 0,\quad z^{\mathsf T}(Gu^* - h) = 0, \qquad (A.3)$$
--   then $u^*$ is a global solution of (A.2).
--   2. If, in addition, $f$ is strictly convex on the feasible set, then any local solution of (A.2) is a global solution, and it is the only global solution.
--
--   Part 1 is the sufficiency half of the KKT theory for convex programs; it is what shows that a solution of the mixed LCP (9.2) yields a solution of the self-dual program (9.1).
--
--   **Formalization Note** The book calls $f$ "smooth" in (A.2); the statement assumes only differentiability at $u^*$, which is what makes $\nabla f(u^*)$ meaningful, so it implies the book's version. Membership $u^* \in U$ is stated explicitly: (A.3) gives $Cu^* = d$ and $Gu^* \ge h$ but not $u^* \in U$, which is part of feasibility. Part 2 (left as an exercise in the book) assumes convex programming plus strict convexity of $f$ on the feasible set, and needs no differentiability. Local and global solutions are as on p. 240, with the Euclidean norm.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 242, Theorem A.2

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem A.2 (p. 242). (A.2) is a convex programming problem (p. 242): `U` is open and
convex and `f` is convex on the feasible set.
(i) If `u* ∈ U`, `f` is differentiable at `u*` and there are `y`, `z` satisfying (A.3a)–(A.3e),
then `u*` is a global solution of (A.2).
(ii) If, in addition, `f` is strictly convex on the feasible set, then any local solution is a
global solution, and it is the only global solution. -/
theorem theorem_A_2 {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hf : ConvexOn ℝ (FeasibleA2 C d G h U) f) :
    (∀ ustar : Fin N → ℝ, ustar ∈ U → DifferentiableAt ℝ f ustar →
      ∀ (y : Fin k → ℝ) (z : Fin l → ℝ),
        gradVec f ustar - Cᵀ *ᵥ y - Gᵀ *ᵥ z = 0 →
        C *ᵥ ustar = d →
        (∀ i, h i ≤ (G *ᵥ ustar) i) →
        (∀ i, 0 ≤ z i) →
        z ⬝ᵥ (G *ᵥ ustar - h) = 0 →
        IsGlobalSolutionA2 f C d G h U ustar) ∧
    (StrictConvexOn ℝ (FeasibleA2 C d G h U) f →
      ∀ ustar : Fin N → ℝ, IsLocalSolutionA2 f C d G h U ustar →
        IsGlobalSolutionA2 f C d G h U ustar ∧
        ∀ u', IsGlobalSolutionA2 f C d G h U u' → u' = ustar) := by sorry

end WrightPDIPM.SelfDual
