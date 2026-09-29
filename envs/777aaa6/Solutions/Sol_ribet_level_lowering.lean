-- Prove2me | solution 1 for ribet_level_lowering
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T05:18:21.204576+00:00
-- url     : https://prove2.me/submissions/cec62c17-8e72-4a0d-b64a-1cc41b4df746
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ribet_level_lowering
import Theorems.Thm_modularity_semistable_elliptic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

-- Sketch: ribet_level_lowering follows from modularity_semistable_elliptic.
-- The Wiles-Ribet argument: given a coprime FLT counterexample (a,b,c,p),
-- the Frey curve is semistable and hence modular (Wiles 1995). By Ribet's
-- ε-conjecture, the associated newform has level dividing 2. But S₂(Γ₀(2)) = 0
-- — contradiction. All of this is encoded in modularity_semistable_elliptic.
theorem solution
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b) (hbc : Nat.Coprime b c) (hac : Nat.Coprime a c)
    (heq : a ^ p + b ^ p = c ^ p) : False :=
  modularity_semistable_elliptic p hp h5 a b c ha hb hc hab hbc hac heq
