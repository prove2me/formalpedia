-- Prove2me | solution 1 for Hirsch.any_segment_summand_le_sharp_width
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T22:16:43.927881+00:00
-- url     : https://prove2.me/submissions/b0af40e2-2e41-42f8-9ec8-044ba3c30a74

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

/-
Target: `Hirsch.any_segment_summand_le_sharp_width` (Open, id 9f931e6d-3190-4c5d-ac47-36d4ad613fca).

The target's preamble *defines* `HirschSegmentSharpPublic.halfspaces` and
`HirschSegmentSharpPublic.segmentSum` inline, so those names are not available to the
server's type check.  The statement below is the target with both definitions
fully inlined:
  `halfspaces a b      = {y | ∀ k, a k y ≤ b k}`
  `segmentSum P g s    = {y | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = p + t • g}`
-/

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : x ∈ {y : E | ∀ k, a k y ≤ b k})
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) = τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s)
    (hdecomp : {y : E | ∀ k, a k y ≤ b k} =
      {y : E | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = p + t • g}) : s ≤ τ := by
  have hx' : x ∈ {y : E | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = p + t • g} := by
    rw [← hdecomp]
    exact hx
  obtain ⟨p, hp, t, ht0, hts, hxpt⟩ := hx'
  have hp0 : ∀ k, a k p ≤ b k := by
    have hp' : p ∈ {y : E | ∀ k, a k y ≤ b k} := by
      rw [hdecomp]
      exact ⟨p, hp, 0, le_rfl, hs, by simp⟩
    exact hp'
  have hp1 : ∀ k, a k (p + s • g) ≤ b k := by
    have hp1' : p + s • g ∈ {y : E | ∀ k, a k y ≤ b k} := by
      rw [hdecomp]
      exact ⟨p, hp, s, hs, le_rfl, rfl⟩
    exact hp1'
  have hb0 := hp0 j
  have hb1 := hp1 i
  have hix := congrArg (fun z : E => a i z) hxpt
  have hjx := congrArg (fun z : E => a j z) hxpt
  simp only [map_add, map_smul, smul_eq_mul] at hb1 hix hjx
  have hfirst : t*(-a j g) ≤ b j - a j x := by nlinarith
  have hlast : (s-t)*(a i g) ≤ b i - a i x := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hfirst hi.le
  have h₂ := mul_le_mul_of_nonneg_left hlast (le_of_lt (neg_pos.mpr hj))
  have hprod : 0 < (a i g)*(-a j g) := mul_pos hi (neg_pos.mpr hj)
  nlinarith [h₁, h₂, hsharp, hprod]

#print axioms solution