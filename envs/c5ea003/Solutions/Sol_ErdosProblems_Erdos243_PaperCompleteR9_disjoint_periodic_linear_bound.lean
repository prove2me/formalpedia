-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR9.disjoint_periodic_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:26:03.507784+00:00
-- url     : https://prove2.me/submissions/374fba58-7f4c-4d07-bdd5-9d53e63a37fd

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR9_disjoint_periodic_count
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
Correct phase-specific modulo-seven obstructions, a sharp
one-in-seven disjoint-block counting certificate, and exact counterexamples
to the stronger phase-free statement in the supplied manuscript.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR9 in
theorem solution (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    ∀ X : ℕ, X ≤ s * exceptionCount E X + (r + s) := by
  classical
  intro X
  by_cases hr : r ≤ X
  · let K := (X - r) / s
    have hdecomp := Nat.mod_add_div (X - r) s
    change (X - r) % s + s * K = X - r at hdecomp
    have hfloor : s * K ≤ X - r := by omega
    have hend : r + s * K ≤ X := by omega
    have hsub : exceptionFinset E (r + s * K) ⊆ exceptionFinset E X := by
      intro x hx
      obtain ⟨hx, hE⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le hend), hE⟩
    have hc : K ≤ exceptionCount E X :=
      (disjoint_periodic_count E r s L hL hhit K).trans (Finset.card_le_card hsub)
    have hrem := Nat.mod_lt (X - r) hs
    have hmul := Nat.mul_le_mul_left s hc
    omega
  · omega
