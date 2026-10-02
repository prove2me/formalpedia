-- Prove2me | Definitions.Def_ZZ_CutoffComplete2
-- name    : ZZ_CutoffComplete2
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T17:52:07.023086+00:00
-- url     : https://prove2.me/theorems/9a553e35-938a-45ba-855b-1745f4d64d26
-- title:
--   p
-- statement:
--   p

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

namespace BookSixth

theorem solution {K O : Set Space3} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) :
    ∃ f : Space3 → ℝ, Continuous f ∧
      (∀ x, x ∈ K → f x = 1) ∧ (∀ x, x ∉ O → f x = 0) := by
  have hTc : IsClosed (Set.compl O) := hO.isClosed_compl
  have hKd : Disjoint K (Set.compl O) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxK
    intro hxO
    exact False.elim (hxO (hKO hxK))
  obtain ⟨f, hf0, hf1, _⟩ :=
    exists_continuous_zero_one_of_isCompact' hK hTc hKd
  exact ⟨(f : Space3 → ℝ), f.continuous, fun x hx => hf1 hx, fun x hxO => hf0 hxO⟩
end BookSixth


