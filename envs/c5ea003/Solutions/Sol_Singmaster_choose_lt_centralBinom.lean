-- Prove2me | solution 1 for Singmaster.choose_lt_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:13:33.520113+00:00
-- url     : https://prove2.me/submissions/5ddb3e0c-a3d7-45fc-b652-f37de393441b

import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
theorem solution {m n k : ℕ} (hm : 1 ≤ m) (hk : k ≤ n) (hn : n ≤ 2 * m)
    (hne : n ≠ 2 * m ∨ k ≠ m) : n.choose k < (2 * m).choose m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rcases Nat.lt_or_ge n (2 * (m' + 1)) with hlt | hge
  · -- a shorter row is dominated by half of the central coefficient (Pascal)
    have hpascal : (2 * (m' + 1)).choose (m' + 1)
        = (2 * m' + 1).choose m' + (2 * m' + 1).choose (m' + 1) := by
      rw [show 2 * (m' + 1) = (2 * m' + 1) + 1 by ring, Nat.choose_succ_succ]
    have h1 : n.choose k ≤ (2 * m' + 1).choose k := Nat.choose_le_choose k (by omega)
    have h2 : (2 * m' + 1).choose k ≤ (2 * m' + 1).choose ((2 * m' + 1) / 2) :=
      Nat.choose_le_middle k _
    have h3 : (2 * m' + 1) / 2 = m' := by omega
    have h4 : 0 < (2 * m' + 1).choose (m' + 1) := Nat.choose_pos (by omega)
    rw [h3] at h2
    omega
  · -- the central row is strictly unimodal
    have hn2 : n = 2 * (m' + 1) := by omega
    subst hn2
    have hkm : k ≠ m' + 1 := by
      rcases hne with h | h
      · exact absurd rfl h
      · exact h
    have hstep : ∀ j, j < m' + 1 →
        (2 * (m' + 1)).choose j < (2 * (m' + 1)).choose (j + 1) := by
      intro j hj
      have hsucc := Nat.choose_succ_right_eq (2 * (m' + 1)) j
      have hpos : 0 < (2 * (m' + 1)).choose j := Nat.choose_pos (by omega)
      obtain ⟨t, ht⟩ : ∃ t, 2 * (m' + 1) - j = j + 2 + t := ⟨2 * (m' + 1) - j - (j + 2), by omega⟩
      rw [ht] at hsucc
      by_contra hle
      push_neg at hle
      have := Nat.mul_le_mul_right (j + 1) hle
      nlinarith
    have hmono : ∀ d j, j + d + 1 = m' + 1 →
        (2 * (m' + 1)).choose j < (2 * (m' + 1)).choose (m' + 1) := by
      intro d
      induction d with
      | zero =>
        intro j hj
        have := hstep j (by omega)
        rwa [show j + 1 = m' + 1 by omega] at this
      | succ d ih =>
        intro j hj
        exact (hstep j (by omega)).trans (ih (j + 1) (by omega))
    rcases Nat.lt_or_gt_of_ne hkm with hlt | hgt
    · exact hmono (m' - k) k (by omega)
    · rw [← Nat.choose_symm hk]
      exact hmono (m' - (2 * (m' + 1) - k)) (2 * (m' + 1) - k) (by omega)
