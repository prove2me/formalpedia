-- Prove2me | solution 2 for rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-25T14:17:29.201321+00:00
-- url     : https://prove2.me/submissions/483b286c-2421-4fac-9611-d18de8661e1d

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Theorems.Thm_centered_operator_symmetrization_q1_bound
import Theorems.Thm_inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max
import Theorems.Thm_expected_sqrt_gram_jensen_assembly
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

namespace ProveCarveB

variable {n₁ n₂ : ℕ}

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The Bernoulli observation weights sum to 1. -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const, Finset.card_compl]

/-- Pulling a constant out of the Bernoulli expectation. -/
theorem bernoulliExpectation_const_mul (p c : ℝ)
    (F : Finset (Fin n₁ × Fin n₂) → ℝ) :
    bernoulliExpectation p (fun Ω => c * F Ω) =
      c * bernoulliExpectation p F := by
  unfold bernoulliExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Ω _
  ring

/-- Monotonicity of `bernoulliExpectation` under `p ∈ [0,1]`. -/
theorem bernoulliExpectation_mono (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F G : Finset (Fin n₁ × Fin n₂) → ℝ)
    (hFG : ∀ Ω, F Ω ≤ G Ω) :
    bernoulliExpectation p F ≤ bernoulliExpectation p G := by
  unfold bernoulliExpectation
  apply Finset.sum_le_sum
  intro Ω _
  exact mul_le_mul_of_nonneg_left (hFG Ω) (weight_nonneg p hp0 hp1 Ω)

end ProveCarveB

open ProveCarveB in
/-- CARVE B — Rudelson 1999 (JFA 164) Thm 1 Steps 1+2 (symmetrization + matrix
non-commutative Khintchine), the expected-operator-norm vs `√(sampled-Gram)`
moment engine, as a reduction onto three children:
* `centered_operator_symmetrization_q1_bound` (Bernoulli → Rademacher sign-average);
* `inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max` (matrix
  Khintchine variance-proxy, with the `2 ≤ max n₁ n₂` hypothesis);
* `expected_sqrt_gram_jensen_assembly` (constant collection / scale rewrite).

`Csym = 2 * Csym0`. The `max n₁ n₂ = 1` edge collapses both sides to `0`
(`√(log 1 / p) = 0` on the right; the centered fluctuation vanishes on the
weighted left). -/
theorem solution :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1 : ℝ) else 0)
                      - (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2)
                          e.1 e.2)))))‖) ≤
          Csym *
            (Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * R)
          * bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega =>
                Real.sqrt
                  (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                      (∑ ab : Fin n₁ × Fin n₂,
                        (if ab ∈ Omega then (1 : ℝ) else 0) •
                          Matrix.vecMulVec
                            (fun e : Fin n₁ × Fin n₂ =>
                              tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                            (fun e : Fin n₁ × Fin n₂ =>
                              tangentProjection S (coordinateMatrix ab.1 ab.2)
                                e.1 e.2))))‖)) := by
  obtain ⟨Csym0, hCsym0pos, hproxy⟩ :=
    inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max
  refine ⟨2 * Csym0, by positivity, ?_⟩
  intro n₁ n₂ r m M S R hn₁ hn₂ hr hm hR hradius
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at this; linarith
  -- abbreviations for the two integrand matrices
  set G : Finset (Fin n₁ × Fin n₂) → Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
    fun Omega =>
      ∑ ab : Fin n₁ × Fin n₂,
        (if ab ∈ Omega then (1 : ℝ) else 0) •
          Matrix.vecMulVec
            (fun e : Fin n₁ × Fin n₂ =>
              tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
            (fun e : Fin n₁ × Fin n₂ =>
              tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
    with hG
  by_cases hmax2 : 2 ≤ max n₁ n₂
  · -- MAIN CASE
    -- Step 1: symmetrization node
    have hsym := centered_operator_symmetrization_q1_bound n₁ n₂ r m M S hn₁ hn₂ hr hm
    -- Step 2: bound the symmetrized RHS by applying the proxy node per Ω.
    -- The proxy gives, for each Ω:
    --   (∑_Es ... ‖signed‖) ≤ Csym0 * (√log·R) * √‖G_Ω‖.
    -- Multiply by p⁻¹ ≥ 0, monotone in the expectation.
    have hpinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
    -- The symmetrized integrand and its bound
    -- symInt Ω := p⁻¹ * (∑_Es (1/2)^card * ‖signed sampled sum‖)
    -- boundInt Ω := p⁻¹ * (Csym0 * (√log·R) * √‖G_Ω‖)
    have hstep2 :
        bernoulliExpectation p
            (fun Omega => p⁻¹ *
              (∑ Es : Finset (Fin n₁ × Fin n₂),
                ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                    (∑ ab : Fin n₁ × Fin n₂,
                      (((if ab ∈ Es then (1:ℝ) else -1) *
                          (if ab ∈ Omega then (1:ℝ) else 0)) •
                        Matrix.vecMulVec
                          (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                          (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)) ≤
          bernoulliExpectation p
            (fun Omega => p⁻¹ *
              (Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R) *
                Real.sqrt
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) := by
      apply bernoulliExpectation_mono p hp0 hp1
      intro Omega
      apply mul_le_mul_of_nonneg_left _ hpinv0
      have := hproxy n₁ n₂ r m M S R hn₁ hn₂ hr hm hmax2 hR hradius Omega
      rw [hG]
      exact this
    -- Step 3: pull the constant out of the bound expectation
    have hpull :
        bernoulliExpectation p
            (fun Omega => p⁻¹ *
              (Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R) *
                Real.sqrt
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) =
          (Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R)) *
            bernoulliExpectation p
              (fun Omega => p⁻¹ *
                Real.sqrt
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖) := by
      rw [← bernoulliExpectation_const_mul p
        (Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R))]
      apply Finset.sum_congr rfl
      intro Ω _
      ring
    -- combine sym + step2 + pull
    -- LHS_target ≤ 2 * (symmetrized) = 2 * E[p⁻¹ * ∑_Es...] ≤ 2 * E[bound] = 2 * Csym0 √log R * E[p⁻¹ √‖G‖]
    have hchain :
        bernoulliExpectation p
            (fun Omega => p⁻¹ *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)
          ≤ 2 * ((Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R)) *
              bernoulliExpectation p
                (fun Omega => p⁻¹ *
                  Real.sqrt
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) := by
      calc _ ≤ 2 * bernoulliExpectation p
                  (fun Omega => p⁻¹ *
                    (∑ Es : Finset (Fin n₁ × Fin n₂),
                      ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                        ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                          (∑ ab : Fin n₁ × Fin n₂,
                            (((if ab ∈ Es then (1:ℝ) else -1) *
                                (if ab ∈ Omega then (1:ℝ) else 0)) •
                              Matrix.vecMulVec
                                (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                                (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)) := hsym
        _ ≤ 2 * bernoulliExpectation p
                (fun Omega => p⁻¹ *
                  (Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R) *
                    Real.sqrt
                      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) := by
              apply mul_le_mul_of_nonneg_left hstep2 (by norm_num)
        _ = _ := by rw [hpull]
    -- now match to the target RHS via the Jensen assembly node
    have hgnn : ∀ Ω : Finset (Fin n₁ × Fin n₂),
        0 ≤ ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Ω)))‖ :=
      fun Ω => norm_nonneg _
    have hjensen := expected_sqrt_gram_jensen_assembly n₁ n₂ m Csym0 R hn₁ hn₂
      (fun Ω => ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Ω)))‖) hgnn
    -- hjensen : 2*Csym0*√log*R * E[p⁻¹*√(g)] = (2*Csym0) * (√(log/p)*R) * E[√(p⁻¹*g)]
    -- The LHS of hchain is exactly the target LHS (after expanding G's signed centering).
    -- 2 * (Csym0*(√log*R) * E[p⁻¹*√‖G‖]) = 2*Csym0*√log*R * E[p⁻¹*√‖G‖]  (assoc)
    -- = RHS of jensen = (2*Csym0)*(√(log/p)*R)*E[√(p⁻¹*‖G‖)] = target RHS.
    calc _ = bernoulliExpectation p
              (fun Omega => p⁻¹ *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
                      Matrix.vecMulVec
                        (fun e : Fin n₁ × Fin n₂ =>
                          tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                        (fun e : Fin n₁ × Fin n₂ =>
                          tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖) := by
            rfl
      _ ≤ 2 * ((Csym0 * (Real.sqrt (Real.log (↑(max n₁ n₂))) * R)) *
              bernoulliExpectation p
                (fun Omega => p⁻¹ *
                  Real.sqrt
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) := hchain
      _ = 2 * Csym0 * Real.sqrt (Real.log (↑(max n₁ n₂))) * R *
              bernoulliExpectation p
                (fun Omega => p⁻¹ *
                  Real.sqrt
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖) := by
            ring
      _ = (2 * Csym0) *
              (Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R) *
              bernoulliExpectation p
                (fun Omega =>
                  Real.sqrt (p⁻¹ *
                    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) := hjensen
      _ = _ := by
            rw [hG]
  · -- EDGE CASE: max n₁ n₂ = 1
    have hmax1 : max n₁ n₂ = 1 := by
      have hlt : max n₁ n₂ < 2 := Nat.lt_of_not_le hmax2
      have hge : 1 ≤ max n₁ n₂ := lt_of_lt_of_le hn₁ (le_max_left _ _)
      omega
    -- log (max n₁ n₂) = 0
    have hlog0 : Real.log (↑(max n₁ n₂)) = 0 := by
      rw [hmax1]; simp
    -- RHS factor √(log/p) = 0
    have hsqrt0 : Real.sqrt (Real.log (↑(max n₁ n₂)) / p) = 0 := by
      rw [hlog0, zero_div, Real.sqrt_zero]
    -- so the whole RHS = 0
    have hrhs0 :
        (2 * Csym0) *
            (Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R)
          * bernoulliExpectation p
              (fun Omega =>
                Real.sqrt (p⁻¹ *
                  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (G Omega)))‖)) = 0 := by
      rw [hsqrt0]; ring
    -- It suffices to prove LHS ≤ 0, then chain to RHS = 0.
    -- We prove LHS = 0 by showing each summand vanishes.
    -- n₁ = n₂ = 1
    have hn1eq : n₁ = 1 := by
      have : n₁ ≤ max n₁ n₂ := le_max_left _ _
      omega
    have hn2eq : n₂ = 1 := by
      have : n₂ ≤ max n₁ n₂ := le_max_right _ _
      omega
    -- LHS = 0
    have hlhs0 :
        bernoulliExpectation p
            (fun Omega => p⁻¹ *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ =>
                        tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖) = 0 := by
      -- m ≤ 1, so p ∈ {0,1}
      subst hn1eq; subst hn2eq
      have hmle1 : m ≤ 1 := by simpa using hm
      -- p = m
      have hpval : p = (m : ℝ) := by rw [hp]; push_cast; simp
      interval_cases m
      · -- m = 0, p = 0, p⁻¹ = 0
        have hp00 : p = 0 := by rw [hpval]; norm_num
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Ω _ => ?_)
        simp only [hp00, inv_zero, zero_mul, mul_zero]
      · -- m = 1, p = 1
        have hp11 : p = 1 := by rw [hpval]; norm_num
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Ω _ => ?_)
        simp only []
        have hsingle : ∀ x : Fin 1 × Fin 1, x = (0,0) := by
          intro x; obtain ⟨a, b⟩ := x; fin_cases a <;> fin_cases b <;> rfl
        by_cases hmem : (0,0) ∈ Ω
        · -- Ω = univ; the matrix sum is 0 (coefficient (1-1)=0)
          have huniv : Ω = Finset.univ :=
            Finset.eq_univ_of_forall (fun x => by rw [hsingle x]; exact hmem)
          have hzeromat :
              (∑ ab : Fin 1 × Fin 1,
                (((if ab ∈ Ω then (1 : ℝ) else 0) - p) •
                  Matrix.vecMulVec
                    (fun e : Fin 1 × Fin 1 =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                    (fun e : Fin 1 × Fin 1 =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))) = 0 := by
            refine Finset.sum_eq_zero (fun ab _ => ?_)
            have : ab ∈ Ω := by rw [huniv]; exact Finset.mem_univ _
            rw [if_pos this, hp11]
            simp
          rw [hzeromat]
          simp
        · -- Ω = ∅; weight = p^0 * (1-p)^(N) but with p=1, (1-1)^(card-0); card=1, so (0)^1 = 0
          have hempty : Ω = ∅ := by
            rw [← Finset.not_nonempty_iff_eq_empty]
            rintro ⟨x, hx⟩; rw [hsingle x] at hx; exact hmem hx
          have hw : bernoulliObservationWeight p Ω = 0 := by
            rw [hempty, hp11]
            unfold bernoulliObservationWeight
            simp
          rw [hw, zero_mul]
    -- chain: LHS = 0 ≤ RHS (= 0)
    rw [hlhs0, hrhs0]

#print axioms solution
