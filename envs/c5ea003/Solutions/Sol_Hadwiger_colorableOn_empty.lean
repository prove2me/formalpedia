-- Prove2me | solution 1 for Hadwiger.colorableOn_empty
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:32:27.110024+00:00
-- url     : https://prove2.me/submissions/93c846e9-1ed1-43b0-9d73-4f41d6df2d09

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerSmallCases

open Hadwiger SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

theorem solution (hk : 0 < k) : ColorableOn G ∅ k := by
  refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
  intro x hx
  cases hx
