-- Prove2me | solution 1 for BanditAlgorithm.bandit_regret_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-18T16:46:52.863771+00:00
-- url     : https://prove2.me/submissions/bf91687c-e018-48a5-9321-7058d5893bc1

import Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
Source-faithful reduction of Lattimore and Szepesvári, *Bandit Algorithms*
(CUP 2020), Lemma 4.5, printed pp. 62--63.  The imported child isolates the
conditional-reward and occupation-count identities proved around Eq. (4.6).
This file performs the remaining gap-weighted finite-sum algebra.
-/

open MeasureTheory ProbabilityTheory

theorem solution {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    BanditAlgorithm.banditRegret ν π n =
      ∑ i, BanditAlgorithm.banditGap ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n) := by
  classical
  rcases BanditAlgorithm.bandit_canonical_occupation_identities ν hInt π n with
    ⟨hreward, hcount⟩
  rw [BanditAlgorithm.banditRegret, hreward]
  simp_rw [BanditAlgorithm.banditGap, sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
  ring
