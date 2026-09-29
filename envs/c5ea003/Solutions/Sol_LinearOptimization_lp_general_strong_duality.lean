-- Prove2me | solution 1 for LinearOptimization.lp_general_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T02:53:21.544083+00:00
-- url     : https://prove2.me/submissions/ed525418-1805-4de2-b0ad-ae9fbe4e2fe7

import Theorems.Thm_LinearOptimization_lp_strong_duality
import Theorems.Thm_LinearOptimization_lp_general_weak_duality
import Mathlib.Tactic

open Matrix
open LinearOptimization

/-- Bertsimas--Tsitsiklis, Theorem 4.18, p. 184, reduced to the proved
ordinary LP strong-duality theorem after stacking the `A` and `D` rows. -/
theorem solution {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (D : Matrix (Fin m₂) (Fin n) ℝ) (d : Fin m₂ → ℝ)
    (xstar : Fin n → ℝ)
    (hopt : IsLpOptimal c {y | b ≤ A.mulVec y ∧ y ∈ polyhedron D d} xstar) :
    ∃ p : Fin m₁ → ℝ, 0 ≤ p ∧
      (∀ q : Fin m₁ → ℝ, 0 ≤ q →
        lagrangeanObjective A b c (polyhedron D d) q ≤
          lagrangeanObjective A b c (polyhedron D d) p) ∧
      lagrangeanObjective A b c (polyhedron D d) p =
        ((c ⬝ᵥ xstar : ℝ) : EReal) := by
  classical
  let e : Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂) := finSumFinEquiv
  let M : Matrix (Fin (m₁ + m₂)) (Fin n) ℝ :=
    fun k j => Sum.elim (fun i => A i j) (fun i => D i j) (e.symm k)
  let B : Fin (m₁ + m₂) → ℝ :=
    fun k => Sum.elim b d (e.symm k)
  let P : GeneralFormLP (m₁ + m₂) n := geFormLP M B c
  have hset : generalFeasibleSet P =
      {y | b ≤ A.mulVec y ∧ y ∈ polyhedron D d} := by
    rw [show generalFeasibleSet P = polyhedron M B by
      simpa [P] using generalFeasibleSet_geFormLP M B c]
    ext y
    constructor
    · intro hy
      constructor
      · intro i
        have hi := hy (e (Sum.inl i))
        simpa [M, B, e, Matrix.mulVec, dotProduct] using hi
      · intro i
        have hi := hy (e (Sum.inr i))
        simpa [M, B, e, Matrix.mulVec, dotProduct] using hi
    · rintro ⟨hyA, hyD⟩ k
      rcases hsk : e.symm k with i | i
      · have hi := hyA i
        simpa [M, B, hsk, Matrix.mulVec, dotProduct] using hi
      · have hi := hyD i
        simpa [M, B, hsk, Matrix.mulVec, dotProduct] using hi
  have hoptP : IsLpOptimal c (generalFeasibleSet P) xstar := by
    simpa [hset] using hopt
  rcases lp_strong_duality P xstar hoptP with ⟨lam, hlamopt, hlam_eq⟩
  have hlamfeas : lam ∈ dualFeasibleGE M c := by
    rw [← dualFeasibleSet_geFormLP M B c]
    simpa [P] using hlamopt.1
  rcases hlamfeas with ⟨hlam0, hMlam⟩
  let p : Fin m₁ → ℝ := fun i => lam (e (Sum.inl i))
  let s : Fin m₂ → ℝ := fun i => lam (e (Sum.inr i))
  have hp : 0 ≤ p := fun i => hlam0 (e (Sum.inl i))
  have hs : 0 ≤ s := fun i => hlam0 (e (Sum.inr i))
  have hdotB : lam ⬝ᵥ B = p ⬝ᵥ b + s ⬝ᵥ d := by
    simp only [dotProduct]
    rw [← e.sum_comp (fun k => lam k * B k)]
    simp [p, s, B, e]
  have htrans : Aᵀ.mulVec p + Dᵀ.mulVec s = c := by
    rw [← hMlam]
    ext j
    change (∑ i, A i j * p i) + (∑ i, D i j * s i) = ∑ k, M k j * lam k
    rw [← e.sum_comp (fun k => M k j * lam k)]
    simp [p, s, M, e]
  have hdualval : p ⬝ᵥ b + s ⬝ᵥ d = c ⬝ᵥ xstar := by
    rw [← hdotB]
    simpa [P, B] using hlam_eq
  have hcost (y : Fin n → ℝ) :
      c ⬝ᵥ y = p ⬝ᵥ A.mulVec y + s ⬝ᵥ D.mulVec y := by
    rw [← htrans]
    rw [add_dotProduct]
    congr 1
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    · simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
  have hlower : ((c ⬝ᵥ xstar : ℝ) : EReal) ≤
      lagrangeanObjective A b c (polyhedron D d) p := by
    unfold lagrangeanObjective
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    norm_cast
    have hDy : d ≤ D.mulVec y := hy
    have hsDy : s ⬝ᵥ d ≤ s ⬝ᵥ D.mulVec y := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hDy i) (hs i)
    rw [← hdualval, hcost y, dotProduct_sub]
    linarith
  have hupper : lagrangeanObjective A b c (polyhedron D d) p ≤
      ((c ⬝ᵥ xstar : ℝ) : EReal) :=
    lp_general_weak_duality A b c D d xstar hopt.1.1 hopt.1.2 p hp
  have heq : lagrangeanObjective A b c (polyhedron D d) p =
      ((c ⬝ᵥ xstar : ℝ) : EReal) := le_antisymm hupper hlower
  refine ⟨p, hp, ?_, heq⟩
  intro q hq
  exact (lp_general_weak_duality A b c D d xstar hopt.1.1 hopt.1.2 q hq).trans_eq heq.symm
