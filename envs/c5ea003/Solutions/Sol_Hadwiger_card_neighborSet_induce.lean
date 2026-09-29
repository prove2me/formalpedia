-- Prove2me | solution 1 for Hadwiger.card_neighborSet_induce
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T07:06:39.040978+00:00
-- url     : https://prove2.me/submissions/601712c4-f915-4137-9a27-869a4614e198

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerSmallCases
open Hadwiger in
theorem solution {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype V] [DecidableEq V]
    {S : Finset V} {v : V} (hv : v ∈ S) :
    Nat.card ((G.induce (↑S : Set V)).neighborSet ⟨v, hv⟩)
      = (S.filter (fun w => G.Adj v w)).card := by
  -- neighbours of `v` inside the induced graph are exactly the `G`-neighbours lying in `S`
  let e : (G.induce (↑S : Set V)).neighborSet ⟨v, hv⟩ ≃ (S.filter (fun w => G.Adj v w)) :=
    { toFun := fun w => ⟨w.1.1, Finset.mem_filter.mpr ⟨w.1.2, w.2⟩⟩
      invFun := fun u => ⟨⟨u.1, (Finset.mem_filter.mp u.2).1⟩, (Finset.mem_filter.mp u.2).2⟩
      left_inv := fun w => rfl
      right_inv := fun u => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
