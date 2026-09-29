-- Prove2me | Theorems.Thm_mme_regional_parent_partition_fine_coordinates
-- name    : mme_regional_parent_partition_fine_coordinates
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:35:23.761573+00:00
-- url     : https://prove2.me/theorems/5fafb1f5-3f64-46a7-a6a6-720d6092f906
-- title:
--   Physical child coordinates agree with literal parent-word splitting
-- statement:
--   Suppose $T$ parent positions are partitioned into regions of sizes $n_r$. There exists an ordering of the $2T$ child positions such that, for every fine word of length $4T$, grouping its letters into length-two child words in that order agrees with grouping into length-four parent words and taking the literal left and right halves. The equality holds at every region, parent position and child side. This identifies the physical coordinate ordering used by extraction with the ordering in the released histogram windows.
-- source:
--   Physical regional partitions and literal complete-word concatenation.

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_regional_parent_partition_fine_coordinates
    {R T : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ Fin T) :
    ∃ childPositions : Fin (T * 2) ≃ Position n,
      ∀ (x : ProfiledCW.FineWord (T * 4)) (p : Position n),
        ProfiledCW.split childPositions (show (T * 2) * 2 ^ (2 - 1) = T * 4 by omega) x p =
          (let v := completeWordSplitEquiv 2 (by decide)
            (ProfiledCW.split (Equiv.refl (Fin T)) rfl x (positions ⟨p.1,p.2.1⟩))
          ![v.1,v.2] p.2.2) := by sorry
