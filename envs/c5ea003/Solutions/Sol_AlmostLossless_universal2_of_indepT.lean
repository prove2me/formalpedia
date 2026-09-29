-- Prove2me | solution 1 for AlmostLossless.universal2_of_indepT
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:56:54.458872+00:00
-- url     : https://prove2.me/submissions/fc1631c0-f6b3-4001-8050-8dfe870b6676

import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
open AlmostLossless in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ} {H : Fin K → α → Fin M}
    (hI : IndepT H 1) : Universal2 H := by
  intro x y hxy
  have h := hI x {y} (Finset.card_singleton y) (by simpa using hxy)
  simp only [Finset.mem_singleton, forall_eq, pow_one] at h
  have hset : (Finset.univ.filter (fun k => H k x = H k y))
      = Finset.univ.filter (fun k => H k y = H k x) := Finset.filter_congr (fun k _ => eq_comm)
  rw [hset]
  exact h
