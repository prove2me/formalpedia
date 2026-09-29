-- Prove2me | solution 1 for Zeta23.ZeroConfig.N_le_two_mul_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:26:39.134142+00:00
-- url     : https://prove2.me/submissions/3de6c3c3-624a-4b92-937d-1b9364d4621d

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

-- from Zeta23.Defs.Counting
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs/Counting.lean — elementary counting facts for an abstract ZeroConfig.
[eq:trivialchain] at the abstract level; Statement.lean transfers it to ζ.
-/

open Set

noncomputable section

namespace Zeta23.ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma window_finite : (Z.window T₁ T₂).Finite := Z.finite_window T₁ T₂



/-- Monotonicity of Σ m_ρ over finite subsets of a window. -/
lemma finsum_mult_mono {s t : Set ℂ} (hst : s ⊆ t) (ht : t ⊆ Z.window T₁ T₂) :
    ∑ᶠ ρ ∈ s, Z.mult ρ ≤ ∑ᶠ ρ ∈ t, Z.mult ρ := by
  have htf : t.Finite := (Z.window_finite T₁ T₂).subset ht
  have hsf : s.Finite := htf.subset hst
  rw [finsum_mem_eq_finite_toFinset_sum _ hsf, finsum_mem_eq_finite_toFinset_sum _ htf]
  apply Finset.sum_le_sum_of_subset
  exact Set.Finite.toFinset_subset_toFinset.mpr hst





end Zeta23.ZeroConfig
end
end

-- from Zeta23.RvM.Halving
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Halving.lean — the reflection-halving lemma.

For an abstract zero configuration Z (invariant under ρ ↦ 1 − ρ̄ with equal multiplicities,
Zeta23/Defs.lean), the zeros in a window T₁ < γ ≤ T₂ with β < 1/2 are mapped injectively by the
reflection onto zeros in the same window with β > 1/2, preserving multiplicity. Hence
    N(T₁,T₂) ≤ 2 · Σ_{window, β ≥ 1/2} m_ρ.
Used in Zeta23/RvM/LocalCount.lean — it lets the Jensen/ZerosBound disc (centre
2 + (t+½)i, radius 1.9·0.84) cover only {1/2 ≤ σ ≤ 1}, so ζ is never evaluated left of σ = 0.19
and the σ > 0 growth bound of Zeta23/RvM/ZetaGrowth.lean suffices (no functional equation / Stirling).
The statement is ℝ-valued to save casts downstream.
-/

open Set

noncomputable section

namespace Zeta23

@[simp] lemma reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
@[simp] lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

@[simp] lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by
  simp [reflect]

lemma reflect_injective : Function.Injective reflect :=
  Function.LeftInverse.injective reflect_reflect

namespace ZeroConfig

variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

lemma reflect_mem_window {ρ : ℂ} (h : ρ ∈ Z.window T₁ T₂) : reflect ρ ∈ Z.window T₁ T₂ :=
  ⟨Z.reflect_mem ρ h.1, by simpa [reflect_im] using h.2⟩


end ZeroConfig
end Zeta23
end
open Set
open Zeta23
open ZeroConfig
variable (Z : ZeroConfig) (T₁ T₂ : ℝ)

theorem solution :
    (Z.N T₁ T₂ : ℝ) ≤ 2 * ∑ᶠ ρ ∈ Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re}, (Z.mult ρ : ℝ) := by
  have hW : (Z.window T₁ T₂).Finite := Z.window_finite T₁ T₂
  set A := Z.window T₁ T₂ ∩ {ρ | ρ.re < 1 / 2} with hAdef
  set B := Z.window T₁ T₂ ∩ {ρ | 1 / 2 ≤ ρ.re} with hBdef
  have hA : A.Finite := hW.subset inter_subset_left
  have hB : B.Finite := hW.subset inter_subset_left
  have hWAB : Z.window T₁ T₂ = A ∪ B := by
    ext ρ
    simp only [hAdef, hBdef, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      rcases lt_or_ge ρ.re (1 / 2) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_setOf_eq] at h1 h2
    linarith
  have hN : Z.N T₁ T₂ = ∑ᶠ ρ ∈ A, Z.mult ρ + ∑ᶠ ρ ∈ B, Z.mult ρ := by
    unfold ZeroConfig.N
    rw [hWAB, finsum_mem_union hdisj hA hB]
  have himage : reflect '' A ⊆ B := by
    rintro _ ⟨ρ, ⟨hρW, hlt⟩, rfl⟩
    refine ⟨Z.reflect_mem_window T₁ T₂ hρW, ?_⟩
    simp only [mem_setOf_eq, reflect_re] at hlt ⊢
    linarith
  have hAB : ∑ᶠ ρ ∈ A, Z.mult ρ ≤ ∑ᶠ ρ ∈ B, Z.mult ρ := by
    calc ∑ᶠ ρ ∈ A, Z.mult ρ = ∑ᶠ ρ ∈ A, Z.mult (reflect ρ) :=
          finsum_mem_congr rfl (fun ρ hρ => (Z.mult_reflect ρ hρ.1.1).symm)
      _ = ∑ᶠ σ ∈ reflect '' A, Z.mult σ := (finsum_mem_image reflect_injective.injOn).symm
      _ ≤ ∑ᶠ σ ∈ B, Z.mult σ := Z.finsum_mult_mono T₁ T₂ himage inter_subset_left
  have hcast : (∑ᶠ ρ ∈ B, (Z.mult ρ : ℝ)) = ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Nat.cast_sum]
  rw [hcast, hN]
  have hAB' : ((∑ᶠ ρ ∈ A, Z.mult ρ : ℕ) : ℝ) ≤ ((∑ᶠ ρ ∈ B, Z.mult ρ : ℕ) : ℝ) := by
    exact_mod_cast hAB
  push_cast
  linarith
