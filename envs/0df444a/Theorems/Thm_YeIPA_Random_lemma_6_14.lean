-- Prove2me | Theorems.Thm_YeIPA_Random_lemma_6_14
-- name    : YeIPA.Random.lemma_6_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:01.42774+00:00
-- url     : https://prove2.me/theorems/2fc5ccdf-7408-497c-936d-3236bd59a3cb
-- title:
--   Lemma 6.14 — (6.5) is feasible iff some partition $A=(A_B,A_N)$ makes (6.12) feasible
-- statement:
--   Let $A$ be a real $m\times n$ matrix of full row rank $m$. Then the homogeneous system (6.5)
--   $$Ax=0,\qquad x\ge0,\qquad x\ne0$$
--   is feasible if and only if there is a partition $A=(A_B,A_N)$, where $A_B$ is an $m\times m$ matrix formed by $m$ distinct columns of $A$ and $A_N$ by the remaining $n-m$ columns, such that system (6.12)
--   $$A_Bx_B+(A_Ne)\,x_{m+1}=0,\qquad x\ne0,\qquad x\ge0$$
--   has a solution $x=(x_B,x_{m+1})\in\mathbb R^{m+1}$. Here $e$ is the all-ones vector, so $A_Ne$ is the sum of the columns in $A_N$.
--
--   The partitions for which (6.12) is feasible are called basic feasible partitions; the lemma reduces the feasibility of (6.5) to a system in $m+1$ unknowns, which is how the chapter analyses a random feasible solution (Theorem 6.15).
--
--   **Formalization Note** The partition is an injection $\sigma$ from $\{1,\dots,m\}$ into the column indices; $A_B$ has columns $a_{\sigma(1)},\dots,a_{\sigma(m)}$ and $A_N$ the columns outside the image (the sum $A_Ne$ is $0$ if there are none). Full row rank, a standing assumption of §6.2 (p. 187), is the hypothesis $\operatorname{rank}A=m$; it forces $m\le n$. This is the statement as printed. When $n=m$ it is false (see finding F1 and the corrected variant `YeIPA.Random.lemma_6_14_corrected`): $A_N$ is empty and $x=(0,\dots,0,1)$ solves (6.12) for every $A$, e.g. $A=(1)$, while (6.5) is infeasible.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 194, Lemma 6.14

import Mathlib
import Definitions.Def_YeIPA_Random_Setting

open Matrix

namespace YeIPA.Random

/-- Lemma 6.14 (Ye 1997, p. 194). System (6.5) `Ax = 0, x ≥ 0, x ≠ 0` is feasible if and only
if there is a partition `A = (A_B, A_N)`, where `A_B` is `m × m` (the columns chosen by an
injection `σ : {1, …, m} → {1, …, n}`), such that system (6.12)
`A_B x_B + (A_N e) x_{m+1} = 0, x ≠ 0, x ≥ 0` is feasible.
Standing hypothesis of §6.2 made explicit: `A` has full row rank `m` (p. 187). -/
theorem lemma_6_14 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (hrank : A.rank = m) :
    (∃ x, IsFeasible65 A x) ↔
      ∃ (σ : Fin m ↪ Fin n) (x : Fin (m + 1) → ℝ), IsFeasible612 A σ x := by sorry

end YeIPA.Random
