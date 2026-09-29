-- Prove2me | solution 1 for AGT.zero_sum_minimax
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:23:37.89069+00:00
-- url     : https://prove2.me/submissions/c09cf540-3ebe-4bf4-b8f9-99bee3aff6ec

import Mathlib
import Definitions.Def_agt_games

open Matrix Finset

/-!
# Von Neumann's minimax theorem for matrix games

`AGT.zero_sum_minimax` from Sion's minimax theorem (`Sion.exists_isSaddlePointOn'`),
plus the identification of the expected payoffs of the two-player zero-sum game with the
bilinear form `p ⬝ᵥ A q`.
-/

namespace AGTMinimax

variable {m n : ℕ}

/-! ## The bilinear form as a pair of linear maps -/

/-- `q ↦ pᵀ A q`, linear in `q`. -/
noncomputable def rowMap (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun q := p ⬝ᵥ A.mulVec q
  map_add' q q' := by simp [Matrix.mulVec_add, dotProduct_add]
  map_smul' c q := by simp [Matrix.mulVec_smul, dotProduct_smul]

/-- `p ↦ pᵀ A q`, linear in `p`. -/
noncomputable def colMap (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun p := p ⬝ᵥ A.mulVec q
  map_add' p p' := by simp [add_dotProduct]
  map_smul' c p := by simp [smul_dotProduct]

theorem rowMap_apply (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) :
    rowMap A p q = p ⬝ᵥ A.mulVec q := rfl

theorem colMap_apply (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) (q : Fin n → ℝ) :
    colMap A q p = p ⬝ᵥ A.mulVec q := rfl

/-! ## The saddle point -/

theorem stdSimplex_nonempty (k : ℕ) : (stdSimplex ℝ (Fin (k + 1))).Nonempty := by
  refine ⟨fun i => if i = 0 then 1 else 0, fun i => ?_, ?_⟩
  · by_cases h : i = 0 <;> simp [h]
  · simp

set_option maxHeartbeats 1000000 in
/-- The saddle point, from Sion's minimax theorem. -/
theorem exists_saddle (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    ∃ q ∈ stdSimplex ℝ (Fin (n + 1)), ∃ p ∈ stdSimplex ℝ (Fin (m + 1)),
      ∀ q' ∈ stdSimplex ℝ (Fin (n + 1)), ∀ p' ∈ stdSimplex ℝ (Fin (m + 1)),
        p' ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q' := by
  classical
  have hcont_row : ∀ p : Fin (m + 1) → ℝ, Continuous (fun q => p ⬝ᵥ A.mulVec q) :=
    fun p => (rowMap A p).continuous_of_finiteDimensional
  have hcont_col : ∀ q : Fin (n + 1) → ℝ, Continuous (fun p => p ⬝ᵥ A.mulVec q) :=
    fun q => (colMap A q).continuous_of_finiteDimensional
  obtain ⟨q, hq, p, hp, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn'
      (X := stdSimplex ℝ (Fin (n + 1))) (Y := stdSimplex ℝ (Fin (m + 1)))
      (f := fun q p => p ⬝ᵥ A.mulVec q)
      (ne_X := stdSimplex_nonempty n) (ne_Y := stdSimplex_nonempty m)
      (cX := convex_stdSimplex ℝ (Fin (n + 1))) (cY := convex_stdSimplex ℝ (Fin (m + 1)))
      (kX := isCompact_stdSimplex ℝ (Fin (n + 1))) (kY := isCompact_stdSimplex ℝ (Fin (m + 1)))
      (hfy := fun p _ => ((hcont_row p).lowerSemicontinuous).lowerSemicontinuousOn _)
      (hfy' := fun p _ => ((rowMap A p).convexOn (convex_stdSimplex ℝ (Fin (n + 1)))).quasiconvexOn)
      (hfx := fun q _ => ((hcont_col q).upperSemicontinuous).upperSemicontinuousOn _)
      (hfx' := fun q _ =>
        ((colMap A q).concaveOn (convex_stdSimplex ℝ (Fin (m + 1)))).quasiconcaveOn)
  exact ⟨q, hq, p, hp, fun q' hq' p' hp' => hsaddle q' hq' p' hp'⟩

/-! ## The expected payoffs of the matrix game -/

/-- A pure profile of the two-player matrix game is a pair of pure strategies. -/
def pairEquiv (m n : ℕ) : (∀ b, AGT.matrixGameStrat m n b) ≃ Fin m × Fin n where
  toFun s := (s true, s false)
  invFun z := fun b => Bool.rec z.2 z.1 b
  left_inv s := by funext b; cases b <;> rfl
  right_inv z := rfl

theorem expected_apply (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ)
    (σ : ∀ b, AGT.matrixGameStrat (m + 1) (n + 1) b → ℝ) (c : Bool) :
    AGT.expectedPayoff (AGT.zeroSumPayoff A) σ c =
      cond c ((σ true) ⬝ᵥ A.mulVec (σ false)) (-((σ true) ⬝ᵥ A.mulVec (σ false))) := by
  classical
  have hdot : (σ true) ⬝ᵥ A.mulVec (σ false)
      = ∑ x, ∑ y, σ true x * σ false y * A x y := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have key : ∀ g : Fin (m + 1) → Fin (n + 1) → ℝ,
      (∑ s : (∀ b, AGT.matrixGameStrat (m + 1) (n + 1) b),
          AGT.profileProb σ s * g (s true) (s false))
        = ∑ x, ∑ y, σ true x * σ false y * g x y := by
    intro g
    refine Eq.trans (Fintype.sum_equiv (pairEquiv (m + 1) (n + 1))
      (fun s => AGT.profileProb σ s * g (s true) (s false))
      (fun z => σ true z.1 * σ false z.2 * g z.1 z.2) ?_) ?_
    · intro s
      simp [AGT.profileProb, pairEquiv, mul_comm]
    · exact Fintype.sum_prod_type _
  cases c with
  | false =>
      show AGT.expectedPayoff (AGT.zeroSumPayoff A) σ false = _
      simp only [AGT.expectedPayoff, AGT.zeroSumPayoff, cond_false, hdot]
      refine Eq.trans (key (fun x y => -(A x y))) ?_
      simp only [mul_neg, Finset.sum_neg_distrib]
  | true =>
      show AGT.expectedPayoff (AGT.zeroSumPayoff A) σ true = _
      simp only [AGT.expectedPayoff, AGT.zeroSumPayoff, cond_true, hdot]
      exact key (fun x y => A x y)

/-! ## The theorem -/

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.11 of *Algorithmic Game Theory*.** -/
theorem zero_sum_minimax (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    ∃ p ∈ stdSimplex ℝ (Fin (m + 1)), ∃ q ∈ stdSimplex ℝ (Fin (n + 1)),
      (∀ p' ∈ stdSimplex ℝ (Fin (m + 1)),
        p' ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q) ∧
      (∀ q' ∈ stdSimplex ℝ (Fin (n + 1)),
        p ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q') ∧
      AGT.IsMixedNash (AGT.zeroSumPayoff A) (AGT.matrixGameProfile p q) := by
  classical
  obtain ⟨q, hq, p, hp, hsaddle⟩ := exists_saddle A
  refine ⟨p, hp, q, hq, fun p' hp' => hsaddle q hq p' hp',
    fun q' hq' => hsaddle q' hq' p hp, ?_, ?_⟩
  · intro c
    cases c with
    | true => exact hp
    | false => exact hq
  · intro c τ hτ
    cases c with
    | true =>
        have h1 : Function.update (AGT.matrixGameProfile p q) true τ true = τ :=
          Function.update_self _ _ _
        have h2 : Function.update (AGT.matrixGameProfile p q) true τ false = q := by
          rw [Function.update_of_ne (by decide)]; rfl
        rw [expected_apply, expected_apply, h1, h2]
        simpa using hsaddle q hq τ ⟨hτ.1, hτ.2⟩
    | false =>
        have h1 : Function.update (AGT.matrixGameProfile p q) false τ true = p := by
          rw [Function.update_of_ne (by decide)]; rfl
        have h2 : Function.update (AGT.matrixGameProfile p q) false τ false = τ :=
          Function.update_self _ _ _
        rw [expected_apply, expected_apply, h1, h2]
        simp only [cond_false, neg_le_neg_iff]
        exact hsaddle τ ⟨hτ.1, hτ.2⟩ p hp

end AGTMinimax


open AGTMinimax

/-- **Theorem 1.11 of *Algorithmic Game Theory***: a finite two-person zero-sum game has
optimal mixed strategies, and they form a mixed Nash equilibrium. -/
theorem solution {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    ∃ p ∈ stdSimplex ℝ (Fin (m + 1)), ∃ q ∈ stdSimplex ℝ (Fin (n + 1)),
      (∀ p' ∈ stdSimplex ℝ (Fin (m + 1)),
        p' ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q) ∧
      (∀ q' ∈ stdSimplex ℝ (Fin (n + 1)),
        p ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q') ∧
      AGT.IsMixedNash (AGT.zeroSumPayoff A) (AGT.matrixGameProfile p q) :=
  AGTMinimax.zero_sum_minimax A
