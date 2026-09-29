-- Prove2me | solution 1 for ScaleSmoothness.sum_dial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:45:33.588718+00:00
-- url     : https://prove2.me/submissions/3fe88af7-b552-4e78-92fe-792646b5d56d

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
open ScaleSmoothness Finset in
theorem solution (p : ℕ) [NeZero p] : ∑ N : ZMod p, dial p N = p := by
  -- summing the fibre sizes of `x ↦ x²` over all values counts the domain
  have h : (Finset.univ : Finset (ZMod p)).card
      = ∑ N ∈ (Finset.univ : Finset (ZMod p)),
        ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = N)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  simp only [dial]
  rw [← h, Finset.card_univ, ZMod.card]
