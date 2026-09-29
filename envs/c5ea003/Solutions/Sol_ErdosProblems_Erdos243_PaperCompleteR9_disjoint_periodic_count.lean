-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR9.disjoint_periodic_count
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:48:40.157619+00:00
-- url     : https://prove2.me/submissions/063ff5a9-fe15-460c-ac8b-f7c127946e09

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
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
    (hL : L ≤ s) (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E)
    (K : ℕ) : K ≤ exceptionCount E (r + s * K) := by
  classical
  choose w hw using hhit
  let F : ℕ → ℕ := fun k ↦ r + s * k + w k
  have hFmono : StrictMono F := by
    intro k l hkl
    have hmul := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hkl)
    have hwk := (hw k).1
    dsimp [F]
    nlinarith
  have hmem : ∀ k ∈ Finset.range K, F k ∈ exceptionFinset E (r + s * K) := by
    intro k hk
    have hkl := Finset.mem_range.mp hk
    have hmul := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hkl)
    have hwk := (hw k).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, (hw k).2⟩
    dsimp [F]
    nlinarith
  have hc := Finset.card_le_card_of_injOn F hmem hFmono.injective.injOn
  simpa [exceptionCount] using hc
