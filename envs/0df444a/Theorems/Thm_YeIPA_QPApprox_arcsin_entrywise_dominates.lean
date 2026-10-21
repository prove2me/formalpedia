-- Prove2me | Theorems.Thm_YeIPA_QPApprox_arcsin_entrywise_dominates
-- name    : YeIPA.QPApprox.arcsin_entrywise_dominates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:40.359013+00:00
-- url     : https://prove2.me/theorems/af88384d-5917-498c-9170-d5d00c2e290d
-- title:
--   Lemma 9.31 — $\arcsin[X]\succeq X$ for $X\succeq0$ with $d(X)\le e$
-- statement:
--   For a real $n\times n$ matrix $X$ let $\arcsin[X]$ be the matrix with entries $\arcsin(x_{ij})$, and let $d(X)=(x_{11},\dots,x_{nn})$. If $X$ is positive semidefinite and every diagonal entry satisfies $x_{jj}\le1$, then
--   $$\arcsin[X]\succeq X,$$
--   that is, $\arcsin[X]-X$ is positive semidefinite.
--
--   (Every entry of such an $X$ satisfies $|x_{ij}|\le\sqrt{x_{ii}x_{jj}}\le1$, so $\arcsin[X]$ is well defined.) This is the matrix inequality that turns the expected value of the sign rounding into a bound in terms of the relaxation in the proof of Theorem 9.33.
--
--   **Formalization Note** The book writes $d(X)\le1$; this is stated as $x_{jj}\le1$ for every $j$. $\succeq$ is Mathlib's `PosSemidef` (symmetric and positive semidefinite). The book leaves the proof as Exercise 9.12.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 328, Lemma 9.31

import Mathlib
import Definitions.Def_YeIPA_QPApprox_Relaxation

open Matrix MeasureTheory

namespace YeIPA.QPApprox

variable {m n : ℕ}

/-- **Lemma 9.31** (Ye, *Interior Point Algorithms*, Wiley 1997, p. 328).

Let `X ⪰ 0` and `d(X) ≤ 1`. Then `arcsin[X] ⪰ X`, i.e. `arcsin[X] − X` is positive
semi-definite, where `arcsin[X]` is the matrix with entries `arcsin(x_ij)`. -/
theorem arcsin_entrywise_dominates (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hd : ∀ j, diagVec X j ≤ 1) :
    (entrywise Real.arcsin X - X).PosSemidef := by sorry

end YeIPA.QPApprox
