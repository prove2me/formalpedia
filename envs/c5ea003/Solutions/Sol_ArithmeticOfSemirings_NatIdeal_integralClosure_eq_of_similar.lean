-- Prove2me | solution 1 for ArithmeticOfSemirings.NatIdeal.integralClosure_eq_of_similar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T12:20:48.051187+00:00
-- url     : https://prove2.me/submissions/323cff94-8949-42d9-95f6-e70ad1007860

import Mathlib
import Definitions.Def_Tropical_ArithmeticOfSemiringsIdeals
open ArithmeticOfSemirings in
theorem solution {A B : Ideal ℕ} (h : NatIdeal.Similar A B) :
    NatIdeal.integralClosure A = NatIdeal.integralClosure B := by
  obtain ⟨C, hC, hAB⟩ := h
  -- `ℕ` has no zero divisors, so a product of nonzero ideals is nonzero
  have hne : ∀ X Y : Ideal ℕ, X ≠ ⊥ → Y ≠ ⊥ → X * Y ≠ ⊥ := by
    intro X Y hX hY
    obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    intro hbot
    have hxy : x * y ∈ X * Y := Ideal.mul_mem_mul hxX hyY
    rw [hbot, Submodule.mem_bot] at hxy
    exact Nat.mul_ne_zero hx0 hy0 hxy
  -- transporting a witness `D` across the similarity: use `C * D`
  have key : ∀ X Y : Ideal ℕ, X * C = Y * C →
      NatIdeal.integralClosure X ⊆ NatIdeal.integralClosure Y := by
    intro X Y hXY r hr
    obtain ⟨D, hD, hle⟩ := hr
    refine ⟨C * D, hne C D hC hD, ?_⟩
    calc Ideal.span {r} * (C * D) = (Ideal.span {r} * D) * C := by ring
      _ ≤ (X * D) * C := by gcongr
      _ = (X * C) * D := by ring
      _ = (Y * C) * D := by rw [hXY]
      _ = Y * (C * D) := by ring
  exact Set.Subset.antisymm (key A B hAB) (key B A hAB.symm)
