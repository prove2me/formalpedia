-- Prove2me | Theorems.Thm_YeIPA_Random_lemma_6_5
-- name    : YeIPA.Random.lemma_6_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:09.141994+00:00
-- url     : https://prove2.me/theorems/2d220d5b-81d4-49d6-b789-45434f01f126
-- title:
--   Lemma 6.5 — for $F=[g,H]$ orthogonal and $v$ uniform on the sphere, $\Pr(\|Hv\|_\infty\le\sqrt{3\log n/n})\to1$
-- statement:
--   For each $n\ge1$ let $F=[g,H]$ be an orthogonal $n\times n$ real matrix, where $g\in\mathbb R^n$ is its first column and $H$ is the $n\times(n-1)$ matrix of its remaining columns; $F$ may depend on $n$ in an arbitrary way. Let $v$ be uniformly distributed on the unit sphere $\{v\in\mathbb R^{n-1}:\|v\|=1\}$, and write $\|w\|_\infty=\max_i|w_i|$. Then
--   $$\Pr\!\left(\|Hv\|_\infty\le\sqrt{\frac{3\log n}{n}}\right)\longrightarrow1\qquad(n\to\infty).$$
--
--   In the one-step analysis of §6.1 the predicted complementarity vector is written as $p=(1+\zeta)g+\eta Hv$ (Lemma 6.4); this lemma controls the largest coordinate of the random part $Hv$, uniformly over the orthogonal completion $H$ of $g$.
--
--   **Formalization Note** The sequence is indexed by $k=n-1\ge0$: for each $k$, `F k` is a $(k+1)\times(k+1)$ real matrix with $F^TF=I$, $H$ is obtained by deleting its first column, and $v$ ranges over the unit sphere of the Euclidean space $\mathbb R^k$ with the normalized surface measure of the module `YeIPA.Random.Setting`. The event $\|Hv\|_\infty\le t$ is written coordinatewise as $|(Hv)_i|\le t$ for all $i$. $\log$ is the natural logarithm. Convergence is in the extended nonnegative reals, to $1$. The statement quantifies over every sequence of orthogonal matrices.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 185, Lemma 6.5

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix MeasureTheory Filter Topology

namespace YeIPA.Random

/-- Lemma 6.5 (Ye 1997, p. 185). Let `F = [g, H]` be an orthogonal `n × n` matrix (`g` its first
column, `H` the `n × (n−1)` matrix of the others). If `v` is uniformly distributed on the unit
sphere in `ℝ^{n−1}`, then `Pr(‖Hv‖_∞ ≤ √(3 log n / n)) → 1` as `n → ∞`.
The matrix may depend on `n` arbitrarily: `n = k + 1`, and `F k` is any orthogonal
`(k+1) × (k+1)` matrix for each `k`. -/
theorem lemma_6_5 (F : (k : ℕ) → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)
    (hF : ∀ k, (F k)ᵀ * F k = 1) :
    Tendsto (fun k : ℕ => uniformSphere k
        {v | ∀ i, |((F k).submatrix id Fin.succ *ᵥ (v : EuclideanSpace ℝ (Fin k)).ofLp) i| ≤
          Real.sqrt (3 * Real.log (k + 1 : ℝ) / (k + 1 : ℝ))})
      atTop (𝓝 1) := by sorry

end YeIPA.Random
