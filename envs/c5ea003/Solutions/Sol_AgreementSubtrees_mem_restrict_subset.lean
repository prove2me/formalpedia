-- Prove2me | solution 1 for AgreementSubtrees.mem_restrict_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:58:18.452993+00:00
-- url     : https://prove2.me/submissions/d2ec3f79-91cf-4ccb-80b4-b16cfdea8e6e

import Mathlib
import Definitions.Def_Novelty_AgreementSubtreesMultiple
import Definitions.Def_Novelty_Core
open AgreementSubtrees in
theorem solution {α : Type*} [DecidableEq α] {T : SplitSystem α} {A s : Finset α}
    (hs : s ∈ restrict T A) : s ⊆ A := by
  -- every restricted split has the form `t ∩ A`
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.inter_subset_right
