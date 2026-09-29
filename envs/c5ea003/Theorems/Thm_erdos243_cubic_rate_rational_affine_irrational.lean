-- Prove2me | Theorems.Thm_erdos243_cubic_rate_rational_affine_irrational
-- name    : erdos243_cubic_rate_rational_affine_irrational
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T13:36:43.347301+00:00
-- url     : https://prove2.me/theorems/43c20ace-bc50-40d7-9557-e2a7c0d1d259
-- title:
--   Rational affine images of cubic-rate reciprocal sums are irrational
-- statement:
--   Let $(a_n)_{n\ge 0}$ be a strictly increasing sequence of positive integers. Assume its reciprocal series has real sum $S$ and that
--
--   $$
--   \lim_{n\to\infty} n^3\left(\frac{a_n^2}{a_{n+1}}-1-\frac{3}{n}\right)=0.
--   $$
--
--   For every pair of rational numbers $r,q$ with $r\ne 0$,
--
--   $$
--   rS+q\notin\mathbb Q.
--   $$
--
--   This records how the proved cubic-rate irrationality theorem behaves under rational changes of scale and origin. The cubic-rate and reciprocal-sum assumptions remain explicit.
--
--   **Formalization Note** The sequence starts at index zero. The displayed limit concerns large indices, while the formal statement uses an explicit `HasSum` premise to name $S$.
-- source:
--   Public cubic-rate theorem: https://prove2.me/theorems/51fbd303-588d-4586-9bbc-f5813513b52c . Pinned Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L67-L77 . Related paper by Will Cook (CC-BY-4.0), including the original Erdős problem and Koizumi prior work: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110 . The paper discloses substantial AI-assisted research and drafting: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188 . New consequence and proof were developed in an isolated public-only reader trial with subsequent owner-side Lean-name repair.

import Mathlib
open Filter

theorem erdos243_cubic_rate_rational_affine_irrational
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 *
        ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv)
    (r q : ℚ) (hr : r ≠ 0) :
    Irrational ((r : ℝ) * Sv + (q : ℝ)) := by sorry
