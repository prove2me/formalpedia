-- Prove2me | Theorems.Thm_erdos243_cubic_rate_every_tail_irrational
-- name    : erdos243_cubic_rate_every_tail_irrational
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T01:55:57.364235+00:00
-- url     : https://prove2.me/theorems/d45dcaf7-5de2-4435-b9ec-5315778b172c
-- title:
--   Every finite reciprocal tail has an irrational sum under the cubic-rate condition
-- statement:
--   Let a be a strictly increasing positive integer sequence satisfying the zero-indexed cubic-rate limit of the proved Erdős #243 theorem, and let Sv be the sum of its reciprocal series. For every finite cutoff N, the reciprocal tail beginning at a(N) has an irrational sum. Removing a finite rational prefix cannot change irrationality. The result retains the cubic-rate and HasSum premises.
-- source:
--   Downstream finite-tail consequence of Will Cook’s proved cubic-rate theorem: https://prove2.me/theorems/51fbd303-588d-4586-9bbc-f5813513b52c . Pinned Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L67-L77 . Related paper by Will Cook (CC-BY-4.0), including the original Erdős problem and Koizumi prior work: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110 . Paper AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188 .

import Mathlib
open Filter

theorem erdos243_cubic_rate_every_tail_irrational
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv)
    (N : ℕ) :
    Irrational (∑' n : ℕ, 1 / (a (n + N) : ℝ)) := by sorry
