-- Prove2me | solution 1 for LinearOptimization.lp_optimal_cost_convex_in_rhs
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T21:52:48.478389+00:00
-- url     : https://prove2.me/submissions/0895dd5a-1896-4cdf-90a9-af8cc7aba593

import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction
import Mathlib.Tactic.Linarith

open Matrix

private lemma feasibleRhsSet_convex {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Convex ℝ (LinearOptimization.feasibleRhsSet A) := by
  intro b₁ hb₁ b₂ hb₂ a d ha hd had
  obtain ⟨x₁, hAx₁, hx₁⟩ := hb₁
  obtain ⟨x₂, hAx₂, hx₂⟩ := hb₂
  refine ⟨a • x₁ + d • x₂, ?_, ?_⟩
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hAx₁, hAx₂]
  · intro j
    exact add_nonneg (mul_nonneg ha (hx₁ j)) (mul_nonneg hd (hx₂ j))

private lemma near_optimal_of_real_value {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (F : (Fin m → ℝ) → ℝ) (b : Fin m → ℝ)
    (hb : b ∈ LinearOptimization.feasibleRhsSet A)
    (hF : ((F b : ℝ) : EReal) = LinearOptimization.lpOptimalCostRhs A c b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ y ∈ LinearOptimization.stdPolyhedron A b, c ⬝ᵥ y < F b + eps := by
  classical
  by_contra hnot
  push_neg at hnot
  have hlower : ((F b + eps : ℝ) : EReal) ≤
      LinearOptimization.lpOptimalCostRhs A c b := by
    rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact EReal.coe_le_coe_iff.mpr (hnot y hy)
  rw [← hF] at hlower
  have : F b + eps ≤ F b := EReal.coe_le_coe_iff.mp hlower
  linarith

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (F : (Fin m → ℝ) → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hdual : (LinearOptimization.dualFeasibleStd A c).Nonempty)
    (hF : ∀ b ∈ LinearOptimization.feasibleRhsSet A,
      ((F b : ℝ) : EReal) = LinearOptimization.lpOptimalCostRhs A c b) :
    ConvexOn ℝ (LinearOptimization.feasibleRhsSet A) F := by
  classical
  refine ⟨feasibleRhsSet_convex A, ?_⟩
  intro b₁ hb₁ b₂ hb₂ a d ha hd had
  by_contra hnot
  have hstrict : a * F b₁ + d * F b₂ < F (a • b₁ + d • b₂) :=
    lt_of_not_ge hnot
  let eps : ℝ := F (a • b₁ + d • b₂) - (a * F b₁ + d * F b₂)
  have heps : 0 < eps := by simpa [eps] using sub_pos.mpr hstrict
  obtain ⟨x₁, hx₁, hcost₁⟩ :=
    near_optimal_of_real_value A c F b₁ hb₁ (hF b₁ hb₁) (eps / 2) (by linarith)
  obtain ⟨x₂, hx₂, hcost₂⟩ :=
    near_optimal_of_real_value A c F b₂ hb₂ (hF b₂ hb₂) (eps / 2) (by linarith)
  have hcomb : a • x₁ + d • x₂ ∈
      LinearOptimization.stdPolyhedron A (a • b₁ + d • b₂) := by
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hx₁.1, hx₂.1]
    · intro j
      exact add_nonneg (mul_nonneg ha (hx₁.2 j)) (mul_nonneg hd (hx₂.2 j))
  have hvalue_le : F (a • b₁ + d • b₂) ≤
      c ⬝ᵥ (a • x₁ + d • x₂) := by
    have hi : LinearOptimization.lpOptimalCostRhs A c (a • b₁ + d • b₂) ≤
        ((c ⬝ᵥ (a • x₁ + d • x₂) : ℝ) : EReal) := by
      rw [LinearOptimization.lpOptimalCostRhs, LinearOptimization.lpValue]
      exact iInf_le_of_le (a • x₁ + d • x₂)
        (iInf_le_of_le hcomb le_rfl)
    rw [← hF (a • b₁ + d • b₂)
      (feasibleRhsSet_convex A hb₁ hb₂ ha hd had)] at hi
    exact EReal.coe_le_coe_iff.mp hi
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    smul_eq_mul] at hvalue_le
  have hweighted : a * (c ⬝ᵥ x₁) + d * (c ⬝ᵥ x₂) <
      a * (F b₁ + eps / 2) + d * (F b₂ + eps / 2) := by
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_mul, zero_add] at had hvalue_le ⊢
      subst d
      simpa using hcost₂
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have haCost := mul_lt_mul_of_pos_left hcost₁ ha'
      by_cases hd0 : d = 0
      · subst d
        simp only [mul_zero, add_zero] at had hvalue_le ⊢
        subst a
        simpa using hcost₁
      · have hd' : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
        exact add_lt_add (mul_lt_mul_of_pos_left hcost₁ ha')
          (mul_lt_mul_of_pos_left hcost₂ hd')
  have hsimplify : a * (F b₁ + eps / 2) + d * (F b₂ + eps / 2) =
      F (a • b₁ + d • b₂) := by
    dsimp [eps]
    nlinarith
  rw [hsimplify] at hweighted
  linarith
