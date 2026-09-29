-- Prove2me | Theorems.Thm_BanditAlgorithm_asymptotic_ucb_schedule_reciprocal_sum_bound
-- name    : BanditAlgorithm.asymptotic_ucb_schedule_reciprocal_sum_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-28T15:25:45.392978+00:00
-- url     : https://prove2.me/theorems/0231ccf1-c53f-47dd-8ef5-1c474f8200e2
-- title:
--   Reciprocal summability of the asymptotic-UCB schedule
-- statement:
--   Let $f(t)=1+t(\log t)^2$ be the exploration schedule used by asymptotically optimal UCB. For every horizon $n\in\mathbb{N}$, its reciprocal weights satisfy
--
--   $$\sum_{t=1}^{n}\frac{1}{f(t)}\leq \frac{5}{2}.$$
--
--   This is the summability estimate requested in Exercise 8.1.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Chapter 8, Exercise 8.1, printed p. 117 / PDF p. 126, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_asymptoticUcbPolicy

theorem BanditAlgorithm.asymptotic_ucb_schedule_reciprocal_sum_bound (n : ℕ) :
    Finset.sum (Finset.Icc 1 n) (fun t ↦ 1 / BanditAlgorithm.asymptoticUcbSchedule t) ≤ 5 / 2 := by sorry
