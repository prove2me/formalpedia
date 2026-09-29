-- Prove2me | solution 1 for PermutationDichotomy.symmetry_barrier_position_read
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:10:11.737404+00:00
-- url     : https://prove2.me/submissions/1a460748-2b46-42ae-ae92-144e2460a403

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy

open scoped BigOperators
open PermutationDichotomy

set_option autoImplicit false

/- Ported from paulklemstine/Lean, commit 53c2925a02,
   Catalog/MachineLearning/TransformerUniversality/PermutationDichotomy.lean.
   The upstream proof is retained; target typeclass binders are declared once. -/
private theorem ported_invariant_defect_lower_bound {ι κ : Type*} {p g : Seq ι κ → ℝ} {σ : Equiv.Perm ι}
    (hp : ∀ x, p (permAct σ x) = p x) (x : Seq ι κ) :
    |g x - g (permAct σ x)| ≤ |p x - g x| + |p (permAct σ x) - g (permAct σ x)| := by
  have h : g x - g (permAct σ x)
      = -(p x - g x) + (p (permAct σ x) - g (permAct σ x)) := by
    rw [hp x]; ring
  calc |g x - g (permAct σ x)|
      ≤ |-(p x - g x)| + |p (permAct σ x) - g (permAct σ x)| := by
        rw [h]; exact abs_add_le _ _
    _ = |p x - g x| + |p (permAct σ x) - g (permAct σ x)| := by rw [abs_neg]

theorem solution {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {σ : Equiv.Perm ι}
    {i₀ : ι} (hne : σ i₀ ≠ i₀) (a₀ : κ) (p : Seq ι κ → ℝ)
    (hp : ∀ x, p (permAct σ x) = p x) :
    ∃ x : Seq ι κ, (1:ℝ)/2 ≤ |p x - x i₀ a₀| := by
  classical
  set u : Seq ι κ := fun i a => if i = i₀ ∧ a = a₀ then (1:ℝ) else 0 with hu
  have hu0 : u i₀ a₀ = 1 := by simp [hu]
  have hv0 : (permAct σ u) i₀ a₀ = 0 := by
    show u (σ i₀) a₀ = 0
    simp [hu, hne]
  have hdefect := ported_invariant_defect_lower_bound (g := fun y : Seq ι κ => y i₀ a₀) hp u
  simp only [hu0, hv0] at hdefect
  by_cases h : (1:ℝ)/2 ≤ |p u - u i₀ a₀|
  · exact ⟨u, h⟩
  · refine ⟨permAct σ u, ?_⟩
    push_neg at h
    rw [hu0] at h
    rw [hv0]
    have habs : |(1:ℝ) - 0| = 1 := by norm_num
    rw [habs] at hdefect
    linarith
