-- Prove2me | solution 1 for TotientShift.S1phi_lt_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:46:46.936034+00:00
-- url     : https://prove2.me/submissions/5c242bed-cee4-4815-8769-2f50e71f3409

import Mathlib
import Definitions.Def_Bridges_TotientUnitShift
set_option maxRecDepth 1000000
open Nat Finset TotientShift in
theorem solution {x : ℕ} (hx : 2 ≤ x) : S1phi x < x := by
  simp only [S1phi]
  have hIcc : (Finset.Icc 1 x).card = x := by rw [Nat.card_Icc]; omega
  -- `φ 2 = 1 ≠ 2 = φ 3`, so `2` witnesses that the filter is strict
  have hss : Finset.filter (fun n => Nat.totient n = Nat.totient (n + 1)) (Finset.Icc 1 x)
      ⊂ Finset.Icc 1 x :=
    Finset.filter_ssubset.mpr ⟨2, Finset.mem_Icc.mpr ⟨by omega, hx⟩, by decide⟩
  calc (Finset.filter (fun n => Nat.totient n = Nat.totient (n + 1)) (Finset.Icc 1 x)).card
      < (Finset.Icc 1 x).card := Finset.card_lt_card hss
    _ = x := hIcc
