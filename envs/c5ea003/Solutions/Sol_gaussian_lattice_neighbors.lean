-- Prove2me | solution 1 for gaussian_lattice_neighbors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:10:01.479596+00:00
-- url     : https://prove2.me/submissions/45c9fbad-de5b-4cb5-92a9-a2e32add6d71

-- Sol generated from Logic/QuantumSystems/DecoderApplications.lean
import Mathlib

/-! # CatalogBuild.Logic.DecoderApplications

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 13
-/














theorem solution(a b : ℤ) :
    a ^ 2 + b ^ 2 = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
                          (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  constructor
  · intro h
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
    have hb2 : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    have ha : a * a ≤ 1 := by nlinarith
    have hb : b * b ≤ 1 := by nlinarith
    have ha_bound : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
    have hb_bound : -1 ≤ b ∧ b ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (b + 1), sq_nonneg (b - 1)]
    rcases ha_bound with ⟨ha_lo, ha_hi⟩
    rcases hb_bound with ⟨hb_lo, hb_hi⟩
    interval_cases a <;> interval_cases b <;> simp_all <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
