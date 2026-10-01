-- Prove2me | Theorems.Thm_ExtendedSmale9_lemma_11_1
-- name    : ExtendedSmale9.lemma_11_1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T14:07:48.43166+00:00
-- url     : https://prove2.me/theorems/5c50243f-f7a5-4824-873a-348e51afa77b
-- title:
--   Lemma 11.1 — solutions of the LP with data $(y_1e_1, A(\alpha,\beta,m,N))$
-- statement:
--   Let $c=\mathbf 1_N$, $m<N$, $N\ge3$, and $\alpha,\beta,y_1>0$. The solution set of the linear program (1.1) with data $(y^A(y_1,m),A(\alpha,\beta,m,N))$ is
--   $$\Xi_{LP}(y^A,A)=\begin{cases}\{\tfrac{y_1}{\alpha\vee\beta}e_1\} & \alpha>\beta,\\ \{\tfrac{y_1}{\alpha\vee\beta}e_2\} & \beta>\alpha,\\ \{\tfrac{y_1}{\alpha\vee\beta}(te_1+(1-t)e_2): t\in[0,1]\} & \alpha=\beta.\end{cases}$$
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §11.1, Lemma 11.1, display (11.2) (pp. 45–46); proof in Appendix A.

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace ExtendedSmale9

theorem lemma_11_1 (m N : ℕ) (hm : 1 ≤ m) (hmN : m < N) (hN : 3 ≤ N)
    (α β y₁ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hy₁ : 0 < y₁) :
    (α > β → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {fun j : Fin N => if (j : ℕ) = 0 then y₁ / max α β else 0}) ∧
    (β > α → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {fun j : Fin N => if (j : ℕ) = 1 then y₁ / max α β else 0}) ∧
    (α = β → lpArgmin (fun _ => 1) (lpVectorA y₁ m) (lpMatrixA α β m N) =
        {z | ∃ t ∈ Set.Icc (0 : ℝ) 1, z = fun j : Fin N =>
          if (j : ℕ) = 0 then y₁ / max α β * t
          else if (j : ℕ) = 1 then y₁ / max α β * (1 - t) else 0}) := by sorry

end ExtendedSmale9
