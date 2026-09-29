-- Prove2me | solution 2 for EnergyAscent.spine_sorted
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:24:07.860212+00:00
-- url     : https://prove2.me/submissions/321dcb10-a1b8-4192-aecf-ab9d17a23c35

import Mathlib
import Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
import Definitions.Def_Combinatorics_EnergyAscentFermatWindow
import Definitions.Def_Combinatorics_EnergyAscentPellSpine
open EnergyAscent in
theorem solution (n : ℕ) :
    ∃ p c : ℤ, 0 < p ∧ 0 < c ∧ IsPT p (p + 1) c ∧ Int.gcd p (p + 1) = 1 ∧
      (n : ℤ) + 5 ≤ c ∧ c < p + (p + 1) := by
  -- the Pell spine `(3,4,5), (20,21,29), (119,120,169), …` via `(p, c) ↦ (3p + 2c + 1, 4p + 3c + 2)`
  have key : ∀ n : ℕ, ∃ p c : ℤ, 3 ≤ p ∧ 0 < c ∧ p ^ 2 + (p + 1) ^ 2 = c ^ 2 ∧ (n : ℤ) + 5 ≤ c := by
    intro n
    induction n with
    | zero => exact ⟨3, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    | succ n ih =>
      obtain ⟨p, c, hp, hc, hpt, hn⟩ := ih
      refine ⟨3 * p + 2 * c + 1, 4 * p + 3 * c + 2, by linarith, by linarith, ?_, ?_⟩
      · linear_combination hpt
      · push_cast
        linarith
  obtain ⟨p, c, hp, hc, hpt, hn⟩ := key n
  refine ⟨p, c, by linarith, hc, hpt, ?_, hn, ?_⟩
  · -- consecutive integers are coprime
    have hcop : IsCoprime p (p + 1) := ⟨-1, 1, by ring⟩
    exact Int.isCoprime_iff_gcd_eq_one.mp hcop
  · -- `c² = 2p² + 2p + 1 < (2p + 1)²`
    by_contra h
    push_neg at h
    nlinarith
