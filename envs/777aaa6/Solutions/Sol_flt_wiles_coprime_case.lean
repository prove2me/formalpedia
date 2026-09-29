-- Prove2me | solution 1 for flt_wiles_coprime_case
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T05:18:19.471918+00:00
-- url     : https://prove2.me/submissions/f5792425-2562-4088-b103-a0c759e6a073
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt_wiles_coprime_case
import Theorems.Thm_ribet_level_lowering
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

-- Sketch: flt_wiles_coprime_case follows from ribet_level_lowering.
-- ribet_level_lowering encapsulates the Frey curve construction + Ribet's ε-conjecture +
-- the emptiness of S₂(Γ₀(2)), giving False from any coprime FLT counterexample.
theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  exact ribet_level_lowering p hp h5 a b c ha hb hc hab hbc hac heq
