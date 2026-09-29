-- Prove2me | solution 1 for TropicalLA.tropEigenvalue_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T09:11:25.269333+00:00
-- url     : https://prove2.me/submissions/9c304cae-2bf2-4f9c-915e-9b7afd7e426c

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ} {lam₁ lam₂ : ℝ}
    {v₁ v₂ : ι → ℝ} (h₁ : IsTropEigen A lam₁ v₁) (h₂ : IsTropEigen A lam₂ v₂) :
    lam₁ = lam₂ := by
  -- an eigenvector gives an upper bound on every entry, and a tight one in every row
  have hup : ∀ (lam : ℝ) (v : ι → ℝ), IsTropEigen A lam v → ∀ i j, A i j + v j ≤ lam + v i := by
    intro lam v h i j
    have hi : Finset.univ.sup' Finset.univ_nonempty (fun k => A i k + v k) = lam + v i := h i
    rw [← hi]
    exact Finset.le_sup' (fun k => A i k + v k) (Finset.mem_univ j)
  have htight : ∀ (lam : ℝ) (v : ι → ℝ), IsTropEigen A lam v →
      ∀ i, ∃ j, A i j + v j = lam + v i := by
    intro lam v h i
    have hi : Finset.univ.sup' Finset.univ_nonempty (fun k => A i k + v k) = lam + v i := h i
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι))
      (fun k => A i k + v k)
    exact ⟨j, by rw [← hi, hj]⟩
  -- compare at an index maximising `v₁ - v₂`; then swap the roles
  have key : ∀ (la lb : ℝ) (va vb : ι → ℝ), IsTropEigen A la va → IsTropEigen A lb vb →
      la ≤ lb := by
    intro la lb va vb ha hb
    obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i => va i - vb i) Finset.univ_nonempty
    obtain ⟨j, hj⟩ := htight la va ha i₀
    have hb' := hup lb vb hb i₀ j
    have hdj : va j - vb j ≤ va i₀ - vb i₀ := hmax j (Finset.mem_univ j)
    linarith
  exact le_antisymm (key lam₁ lam₂ v₁ v₂ h₁ h₂) (key lam₂ lam₁ v₂ v₁ h₂ h₁)
