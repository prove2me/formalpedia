-- Prove2me | Theorems.Thm_YeIPA_Geometry_central_path_objective_monotone
-- name    : YeIPA.Geometry.central_path_objective_monotone
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:57.308148+00:00
-- url     : https://prove2.me/theorems/2b5179cc-a925-497e-b033-85d7c366459e
-- title:
--   Theorem 2.17 (ii) — objectives strictly monotone along the central path (as printed)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $n>m$, have rank $m$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose that both $(LP)$ $\min\{c^Tx: Ax=b,\ x\ge0\}$ and $(LD)$ $\max\{b^Ty: A^Ty+s=c,\ s\ge0\}$ have interior feasible points. For $\mu>0$ let $(x(\mu),y(\mu),s(\mu))$ be a central path point: $x(\mu)>0$, $Ax(\mu)=b$, $s(\mu)>0$, $A^Ty(\mu)+s(\mu)=c$ and $x(\mu)_js(\mu)_j=\mu$ for every $j$.
--
--   Then for $0<\mu'<\mu$,
--   $$c^Tx(\mu')<c^Tx(\mu)\qquad\text{and}\qquad b^Ty(\mu')>b^Ty(\mu).$$
--
--   As $\mu$ decreases along the central path the primal objective decreases and the dual objective increases, so the path moves toward the optimal faces of both programs.
--
--   **Formalization Note** This is the statement as printed, whose proof the book leaves as an exercise. Findings F1, F8 and F6 show that both strict inequalities fail when the corresponding objective is constant on its feasible region (for instance $c=0$, or $b=0$), so the statement is expected to be false; `YeIPA.Geometry.central_path_objective_monotone_corrected` states the weak inequalities. The hypotheses $\operatorname{rank}A=m$ and $n>m$ are the chapter's standing assumptions (p. 48); the rank makes $y(\mu)$ unique.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 72, Theorem 2.17 (ii)

import Mathlib
import Definitions.Def_YeIPA_Geometry_CentralPath

open Matrix

namespace YeIPA.Geometry

/-- Theorem 2.17 (ii) (Ye 1997, p. 72), as printed. Let `A` have rank `m`, with `n > m` (p. 48) and let (LP)
and (LD) both have interior feasible points. For `0 < μ' < μ` and central path points
`(x(μ'), y(μ'), s(μ'))`, `(x(μ), y(μ), s(μ))`:
`cᵀx(μ') < cᵀx(μ)` and `bᵀy(μ') > bᵀy(μ)`. (See FINDINGS.yaml F1, F6: false as printed.) -/
theorem central_path_objective_monotone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hrank : A.rank = m) (hmn : m < n)
    (hP : ∃ x, PrimalInterior A b x) (hD : ∃ y s, DualInterior A c y s)
    (μ' μ : ℝ) (hμ' : 0 < μ') (hμ'μ : μ' < μ)
    (x' : Fin n → ℝ) (y' : Fin m → ℝ) (s' : Fin n → ℝ)
    (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (h' : IsCentralPathPoint A b c μ' x' y' s') (h : IsCentralPathPoint A b c μ x y s) :
    c ⬝ᵥ x' < c ⬝ᵥ x ∧ b ⬝ᵥ y < b ⬝ᵥ y' := by sorry

end YeIPA.Geometry
