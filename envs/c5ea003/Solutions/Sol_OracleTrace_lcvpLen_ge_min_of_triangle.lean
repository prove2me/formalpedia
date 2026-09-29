-- Prove2me | solution 1 for OracleTrace.lcvpLen_ge_min_of_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:21:28.595571+00:00
-- url     : https://prove2.me/submissions/026e1def-4f86-4bd0-98ce-10297b816d43

-- Sol generated from Bridges/LongestCommonValuedPrefix.lean
import Mathlib
import Definitions.Def_Bridges_LongestCommonValuedPrefix
import Theorems.Thm_OracleTrace_lcvpLen_maximal_prefix
import Theorems.Thm_OracleTrace_lcvpLen_symmetric
import Theorems.Thm_OracleTrace_take_eq_of_le_lcvpLen
/-
  # Longest Common Valued Prefix — Foundational Combinatorics

  Bridge: connects ultrametric valuation geometry to prefix-agreement
  combinatorics on finite lists. Defines `lcvpLen` and proves its core
  algebraic properties including the min-prefix (ultrametric valuation)
  inequality.

  Keywords: ultrametric, valuation, prefix_agreement, non_archimedean
-/

open List Finset

open OracleTrace

/-! ## Core Definitions -/




variable {α : Type*} [DecidableEq α]

/-! ## Foundational Recursion -/

@[simp]
theorem lcvpLen_nil_left (u : List α) :
    lcvpLen ([] : List α) u = 0 := by
  simp [lcvpLen]

@[simp]
theorem lcvpLen_nil_right (u : List α) :
    lcvpLen u ([] : List α) = 0 := by
  cases u <;> simp [lcvpLen]



/-! ## Symmetry -/


/-! ## Length Bounds -/

theorem lcvpLen_le_left (u v : List α) :
    lcvpLen u v ≤ u.length := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v =>
      simp only [lcvpLen, List.length_cons]
      by_cases h : a = b
      · simp [h]; exact ih v
      · simp [h]

theorem lcvpLen_le_right (u v : List α) :
    lcvpLen u v ≤ v.length := by
  rw [lcvpLen_symmetric]; exact lcvpLen_le_left v u


/-! ## Self-agreement -/


/-! ## Prefix Agreement Characterization -/



/-! ## Maximality -/



/-! ## Equality Detection -/



/-! ## The Ultrametric Valuation Inequality -/


/-! ## Concatenation Principle -/



open OracleTrace in
theorem solution(u v w : List α) :
    min (lcvpLen u v) (lcvpLen v w) ≤ lcvpLen u w := by
  set k := min (lcvpLen u v) (lcvpLen v w)
  have h1 : k ≤ lcvpLen u v := Nat.min_le_left _ _
  have h2 : k ≤ lcvpLen v w := Nat.min_le_right _ _
  have hkbound : k ≤ min u.length w.length := by
    exact Nat.le_min.mpr ⟨le_trans h1 (lcvpLen_le_left u v),
      le_trans h2 (lcvpLen_le_right v w)⟩
  exact lcvpLen_maximal_prefix u w k hkbound
    ((take_eq_of_le_lcvpLen h1).trans (take_eq_of_le_lcvpLen h2))
