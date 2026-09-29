-- Prove2me | solution 1 for CRTSplitNoGo.polyOrbit_cast
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:45:11.935029+00:00
-- url     : https://prove2.me/submissions/e346c46b-5fc7-4488-b672-777f5ed69e07

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
open CRTSplitNoGo Polynomial in
theorem solution (f : ℤ[X]) (m : ℕ) (x0 : ℤ) (n : ℕ) :
    ((polyOrbit f x0 n : ℤ) : ZMod m) = modOrbit f m x0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- reduction mod `m` commutes with evaluating the integer polynomial
    simp only [polyOrbit, modOrbit, Function.iterate_succ_apply'] at ih ⊢
    rw [← ih, Polynomial.eval_intCast_map]
    simp
