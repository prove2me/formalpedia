-- Prove2me | Theorems.Thm_YeIPA_WorstCase_xi_pos
-- name    : YeIPA.WorstCase.xi_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:57:27.548987+00:00
-- url     : https://prove2.me/theorems/225785cf-a6eb-4b81-ac1d-5bbd70e16b02
-- title:
--   Display (5.3) — with an interior point, the optimal faces are strictly feasible, the maxima over them are attained, and ξ(A, b, c) > 0
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ with $n\ge1$, $b\in\mathbb R^m$, $c\in\mathbb R^n$, and suppose (LP) $\min\{c^Tx:Ax=b,x\ge0\}$ and (LD) $\max\{b^Ty:A^Ty+s=c,s\ge0\}$ have an interior point $(x,y,s)$: $Ax=b$, $x>0$, $A^Ty+s=c$, $s>0$. Let $(P^*,Z^*)$ be the strict complementarity partition and $\Omega_p$, $\Omega_d$ the primal and dual optimal faces. Then
--
--   1. the optimal faces have strictly feasible solutions: some $x^*\in\Omega_p$ has $x^*_j>0$ for every $j\in P^*$, and some $(y^*,s^*)\in\Omega_d$ has $s^*_j>0$ for every $j\in Z^*$;
--   2. for every $j\in P^*$, $\max_{x\in\Omega_p}x_j$ is attained and positive;
--   3. for every $j\in Z^*$, $\max_{(y,s)\in\Omega_d}s_j$ is attained and positive;
--   4. the condition number is positive:
--   $$\xi(A,b,c)=\min\Big\{\min_{j\in P^*}\max_{x\in\Omega_p}x_j,\ \min_{j\in Z^*}\max_{(y,s)\in\Omega_d}s_j\Big\}>0.$$
--
--   These are the claims of display (5.3) and the sentence before it; $\xi$ measures how far the optimal faces reach into the interior of the orthant, and it controls the termination result, Theorem 5.3.
--
--   **Formalization Note** "Attained" is stated as: some point of the face has $j$-th coordinate equal to Lean's `sSup` of that coordinate over the face, and no point of the face exceeds it. The interior point is the hypothesis under which the book calls the faces strictly feasible (p. 153); $n\ge1$ excludes the empty minimum.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 153, display (5.3)

import Mathlib
import Definitions.Def_YeIPA_WorstCase_Termination

open Matrix

namespace YeIPA.WorstCase

/-- Display (5.3) (Ye 1997, p. 153). If (LP) and (LD) have an interior point `(x, y, s)`
(`Ax = b`, `x > 0`, `Aᵀy + s = c`, `s > 0`) and `n ≥ 1`, then the optimal faces have strictly
feasible solutions (some `x* ∈ Ω_p` with `x*_{P*} > 0`, some `(y*, s*) ∈ Ω_d` with `s*_{Z*} > 0`),
every maximum `max_{x ∈ Ω_p} x_j` (`j ∈ P*`) and `max_{(y,s) ∈ Ω_d} s_j` (`j ∈ Z*`) is attained
and positive, and `ξ(A, b, c) = min {ξ_p(A, b, c), ξ_d(A, b, c)} > 0`. -/
theorem xi_pos {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hn : 0 < n) (x : Fin n → ℝ) (y : Fin m → ℝ) (s : Fin n → ℝ)
    (hint : IsInterior A b c x y s) :
    (∃ xs ∈ OmegaP A b c, ∀ j ∈ Pstar A b c, 0 < xs j) ∧
    (∃ p ∈ OmegaD A b c, ∀ j ∈ Zstar A b c, 0 < p.2 j) ∧
    (∀ j ∈ Pstar A b c, ∃ xs ∈ OmegaP A b c, xs j = maxPrimalCoord A b c j ∧
        0 < maxPrimalCoord A b c j ∧ ∀ x' ∈ OmegaP A b c, x' j ≤ xs j) ∧
    (∀ j ∈ Zstar A b c, ∃ p ∈ OmegaD A b c, p.2 j = maxDualCoord A b c j ∧
        0 < maxDualCoord A b c j ∧ ∀ p' ∈ OmegaD A b c, p'.2 j ≤ p.2 j) ∧
    0 < xi A b c := by sorry

end YeIPA.WorstCase
