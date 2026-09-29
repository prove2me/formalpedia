-- Prove2me | solution 1 for Bridges.AttentionKneeGeometry.knee_le_of_geometric_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:19:31.368984+00:00
-- url     : https://prove2.me/submissions/a83d2466-f6b4-49bf-bb59-81418b32086a

import Mathlib
import Definitions.Def_Bridges_AttentionKneeGeometry
open Bridges.AttentionKneeGeometry in
theorem solution {w : ℕ → ℝ} {g C r : ℝ} {N : ℕ}
    (htail : ∀ k, 1 - mass w k ≤ C * r ^ k) (hcert : C * r ^ N ≤ 1 - g) :
    knee w g ≤ N := by
  -- the tail certificate makes `N` keys pass the gate
  have hpass : g ≤ mass w N := by
    have := htail N
    linarith
  exact Nat.sInf_le hpass
