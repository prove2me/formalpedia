-- Prove2me | solution 1 for LFunctionUniverse.complex_coefficient_sequences_not_countable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:43:13.630649+00:00
-- url     : https://prove2.me/submissions/0b3f7e9b-1862-4797-b29b-f5ce5ca34117

-- Sol generated from Applications/LFunctionUniverse/Synthesis.lean
import Mathlib
import Definitions.Def_Applications_LFunctionUniverse_Synthesis

/-!
# A rigorous countability criterion for arithmetic L-function families

This file isolates the exact logical content of a “finite arithmetic census”.  It
does **not** assume that every analytic Selberg-class function has such an encoding.
Instead, it proves that whenever a family admits a faithful encoding by finite lists
over countable alphabets, that family is countable.  If it also contains a faithful
copy of `ℕ`, then it is countably infinite.

The distinction matters: proving a finite-data rigidity theorem for the analytic
Selberg class is a separate, deep mathematical problem.
-/

open LFunctionUniverse








open LFunctionUniverse in
theorem solution: ¬ Countable (ℕ → ℂ) := by
  intro h
  have hb : Countable (ℕ → Bool) := by
    apply Function.Injective.countable
      (f := fun a : ℕ → Bool => fun n => if a n then (1 : ℂ) else 0)
    intro a b hab
    funext n
    have hn := congrFun hab n
    by_cases ha : a n <;> by_cases hb : b n <;> simp [ha, hb] at hn ⊢
  have hcard : Cardinal.mk (ℕ → Bool) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hb
  rw [Cardinal.mk_arrow] at hcard
  simp only [Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id] at hcard
  exact absurd hcard (not_le.mpr (Cardinal.cantor' _ (by norm_num)))
