-- Prove2me | solution 1 for Spike.Quantile.prefix_eq_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:28:04.78936+00:00
-- url     : https://prove2.me/submissions/bf7e058d-14fd-4777-b911-15124cd3e452

import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity
open Spike Spike.Quantile Finset in
theorem solution {N : ℕ} {c : ℕ} (hc : Nat.sqrt N + 1 ≤ c) :
    (window N).filter (fun j => j ≤ c)
      = (window N).filter (fun j => residue N j ≤ residue N c) := by
  -- above `√N` the residue `j² − N` has no truncation, so it orders like `j`
  have hsq : N < (Nat.sqrt N + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt N
    rw [sq]
    exact this
  have hcN : N ≤ c ^ 2 :=
    le_of_lt (lt_of_lt_of_le hsq (Nat.pow_le_pow_left hc 2))
  apply filter_congr
  intro j _
  unfold residue
  rw [tsub_le_tsub_iff_right hcN, Nat.pow_le_pow_iff_left (by norm_num)]
