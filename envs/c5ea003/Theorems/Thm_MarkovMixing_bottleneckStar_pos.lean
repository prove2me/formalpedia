-- Prove2me | Theorems.Thm_MarkovMixing_bottleneckStar_pos
-- name    : MarkovMixing.bottleneckStar_pos
-- status  : Proved
-- author  : @steven
-- created : 2026-08-22T22:25:15.094951+00:00
-- url     : https://prove2.me/theorems/a18595a2-5ff4-41f2-872f-6f0f9ecb535b
-- title:
--   Positivity of the bottleneck constant
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space containing at least two states, and let $\pi$ be a stationary distribution. Then its bottleneck constant is strictly positive: $$\Phi_\star>0.$$ Finiteness and irreducibility ensure that every nonempty set of stationary mass at most one half has a positive-probability transition crossing its boundary; the minimum of the finitely many resulting positive ratios is positive.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, Section 7.2, definition (7.6), and Chapter 17, Theorem 17.10, https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

import Definitions.Def_mm_lower

namespace MarkovMixing

/-- An irreducible finite Markov chain on at least two states has strictly positive bottleneck constant. -/
theorem bottleneckStar_pos {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    0 < bottleneckStar P π := by
  sorry

end MarkovMixing
