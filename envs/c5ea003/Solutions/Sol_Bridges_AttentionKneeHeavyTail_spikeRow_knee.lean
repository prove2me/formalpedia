-- Prove2me | solution 1 for Bridges.AttentionKneeHeavyTail.spikeRow_knee
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T00:56:20.128985+00:00
-- url     : https://prove2.me/submissions/c18c197a-9231-4f0a-9e72-07b94a30fa03

import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
import Definitions.Def_Bridges_AttentionKneeHeavyTail
open Bridges.AttentionKneeGeometry Bridges.AttentionKneeHeavyTail in
theorem solution {m : ℕ} (hm : 1 ≤ m) : knee (spikeRow m) (3 / 4) = m + 1 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- closed form on the plateau: the spike plus `j` plateau keys
  have hmass : ∀ j : ℕ, j ≤ 2 * m → mass (spikeRow m) (j + 1) = 1 / 2 + j / (4 * m) := by
    intro j
    induction j with
    | zero => intro _; simp [mass, spikeRow]
    | succ j ih =>
      intro hj
      have h1 : spikeRow m (j + 1) = 1 / (4 * m) := by
        simp only [spikeRow]
        rw [if_neg (by omega : j + 1 ≠ 0), if_pos (by omega : j + 1 ≤ 2 * m)]
      have ih' := ih (by omega)
      unfold mass at ih' ⊢
      rw [Finset.sum_range_succ, ih', h1]
      push_cast
      field_simp
      ring
  -- `m + 1` keys reach the gate exactly
  have hmem : (3 / 4 : ℝ) ≤ mass (spikeRow m) (m + 1) := by
    rw [hmass m (by omega)]
    rw [show (m : ℝ) / (4 * m) = 1 / 4 by field_simp]
    norm_num
  unfold knee
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · -- fewer keys fall short of the gate
    apply le_csInf ⟨m + 1, hmem⟩
    intro k hk
    by_contra hlt
    push_neg at hlt
    simp only [Set.mem_setOf_eq] at hk
    rcases k with _ | j
    · simp [mass] at hk
      norm_num at hk
    · rw [hmass j (by omega)] at hk
      have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast (by omega : j + 1 ≤ m)
      have : (j : ℝ) / (4 * m) < 1 / 4 := by
        rw [div_lt_iff₀ (by positivity)]
        linarith
      linarith
