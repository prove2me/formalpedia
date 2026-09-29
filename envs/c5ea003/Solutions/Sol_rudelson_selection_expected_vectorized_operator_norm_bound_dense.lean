-- Prove2me | solution 1 for rudelson_selection_expected_vectorized_operator_norm_bound_dense
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T04:22:18.343235+00:00
-- url     : https://prove2.me/submissions/6bdb30ab-2559-4a71-8b16-ede254d6c3e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
import Theorems.Thm_rudelson_selection_sampled_gram_self_bound_dense
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 1000000

/-
NB-4 — `rudelson_selection_expected_vectorized_operator_norm_bound_dense`,
the CORRECT Rudelson §9.1 route (CR2009 / Rudelson 1999 JFA 164 Thm 1).

The OUTER sample expectation is kept a FIRST moment throughout.  The whole
operator-space content is isolated into two carved Open sub-nodes:
  * carve B (`..._symmetrized_gram_sqrt_moment_engine_dense`): Steps 1+2
    (symmetrization + matrix non-commutative Khintchine), giving
      𝔼_Ω[p⁻¹‖A_Ω‖]  ≤  Csym·(√(log N/p)·R)·𝔼_Ω[√(p⁻¹‖G_Ω‖)],
  * carve A (`..._sampled_gram_self_bound_dense`): the eq(2.1) self-bound feed
      ‖G_Ω‖  ≤  p·(Z_Ω + 1).
The solution's OWN logic = pointwise √-monotonicity (carve A) + the outer
concave √-Jensen 𝔼[√(Z+1)] ≤ √(𝔼[Z]+1), both routine.

`A_Ω = ∑_{ab}(δ_ab−p) y_ab⊗y_ab`,  `G_Ω = ∑_{ab∈Ω} y_ab⊗y_ab`,
`y_ab = P_T(e_a e_b*)`,  `Z_Ω = tangentSamplingDeviation Ω S p`,  `p = m/(n₁n₂)`.
-/
theorem solution :
    ∃ Csym : ℝ, 0 < Csym ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        0 ≤ R →
        (m : ℝ) ≥ β * (↑(max n₁ n₂)) * (r : ℝ) * Real.log (↑(max n₁ n₂)) →
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
          * Real.sqrt
              (bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (fun Omega =>
                  tangentSamplingDeviation Omega S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) + 1) := by
  obtain ⟨Csym, hCsym_pos, hEng⟩ :=
    rudelson_selection_symmetrized_gram_sqrt_moment_engine_dense
  refine ⟨Csym, hCsym_pos, ?_⟩
  intro β hβ n₁ n₂ r m M S R hn1 hn2 hr hm hR hdens hcoord
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- 0 < p ≤ 1.
  have hn1R : (0:ℝ) < (n₁ : ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂ : ℝ) := by exact_mod_cast hn2
  have hmRle : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    rwa [Nat.cast_mul] at this
  have hp_nn : 0 ≤ p := by rw [hp_def]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]; exact hmRle
  have hpinv_nn : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_nn
  -- Abbreviations for the per-Ω sampled-Gram operator-norm `‖G_Ω‖`.
  set GnormOf : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Omega =>
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
        (∑ ab : Fin n₁ × Fin n₂,
          (if ab ∈ Omega then (1 : ℝ) else 0) •
            Matrix.vecMulVec
              (fun e : Fin n₁ × Fin n₂ =>
                tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
              (fun e : Fin n₁ × Fin n₂ =>
                tangentProjection S (coordinateMatrix ab.1 ab.2)
                  e.1 e.2))))‖
    with hGnorm_def
  -- The sqrt-prefactor `Csym·(√(log N/p)·R)` is nonnegative.
  set pref : ℝ := Csym * (Real.sqrt (Real.log (↑(max n₁ n₂)) / p) * R) with hpref_def
  have hpref_nn : 0 ≤ pref := by
    rw [hpref_def]
    exact mul_nonneg hCsym_pos.le (mul_nonneg (Real.sqrt_nonneg _) hR)
  -- ===== carve B: the engine bound. =====
  have hstepB :
      bernoulliExpectation p
          (fun Omega =>
            p⁻¹ *
            ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
              (∑ ab : Fin n₁ × Fin n₂,
                (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
                  Matrix.vecMulVec
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2)
                        e.1 e.2)))))‖)
        ≤ pref *
            bernoulliExpectation p
              (fun Omega => Real.sqrt (p⁻¹ * GnormOf Omega)) :=
    hEng n₁ n₂ r m M S R hn1 hn2 hr hm hR hcoord
  -- ===== carve A + sqrt-monotonicity: pointwise √(p⁻¹‖G_Ω‖) ≤ √(Z_Ω+1). =====
  have hpointwise :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        Real.sqrt (p⁻¹ * GnormOf Omega)
          ≤ Real.sqrt (tangentSamplingDeviation Omega S p + 1) := by
    intro Omega
    apply Real.sqrt_le_sqrt
    -- `p⁻¹·‖G_Ω‖ ≤ p⁻¹·(p·(Z+1)) = Z+1`.
    have hGbound : GnormOf Omega ≤ p * (tangentSamplingDeviation Omega S p + 1) := by
      rw [hGnorm_def]
      exact rudelson_selection_sampled_gram_self_bound_dense S Omega p hp_nn hp_le_one
    calc p⁻¹ * GnormOf Omega
        ≤ p⁻¹ * (p * (tangentSamplingDeviation Omega S p + 1)) :=
          mul_le_mul_of_nonneg_left hGbound hpinv_nn
      _ = (p⁻¹ * p) * (tangentSamplingDeviation Omega S p + 1) := by ring
      _ ≤ 1 * (tangentSamplingDeviation Omega S p + 1) := by
            apply mul_le_mul_of_nonneg_right
            · exact inv_mul_le_one
            · -- `0 ≤ Z + 1`.
              have hZnn : 0 ≤ tangentSamplingDeviation Omega S p := by
                unfold tangentSamplingDeviation
                apply Real.sSup_nonneg
                rintro v ⟨X, _, _, rfl⟩
                exact mul_nonneg hpinv_nn (Real.sqrt_nonneg _)
              linarith
      _ = tangentSamplingDeviation Omega S p + 1 := by rw [one_mul]
  -- 𝔼[√(p⁻¹‖G‖)] ≤ 𝔼[√(Z+1)]  (monotone expectation, weights ≥ 0).
  have hw0 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ bernoulliObservationWeight p Omega := by
    intro Omega; unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp_nn _) (pow_nonneg (by linarith) _)
  have hw1 : ∑ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega = 1 := by
    unfold bernoulliObservationWeight
    have huniv : (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂)))
        = (Finset.univ : Finset (Fin n₁ × Fin n₂)).powerset := by
      ext S; simp
    rw [huniv, ← Finset.card_univ, Finset.sum_pow_mul_eq_add_pow]; simp
  have hExpMono :
      bernoulliExpectation p (fun Omega => Real.sqrt (p⁻¹ * GnormOf Omega))
        ≤ bernoulliExpectation p
            (fun Omega => Real.sqrt (tangentSamplingDeviation Omega S p + 1)) := by
    unfold bernoulliExpectation
    apply Finset.sum_le_sum
    intro Omega _
    exact mul_le_mul_of_nonneg_left (hpointwise Omega) (hw0 Omega)
  -- ===== S9: concave √-Jensen  𝔼[√(Z+1)] ≤ √(𝔼[Z]+1). =====
  have hZnn : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ tangentSamplingDeviation Omega S p := by
    intro Omega
    unfold tangentSamplingDeviation
    apply Real.sSup_nonneg
    rintro v ⟨X, _, _, rfl⟩
    exact mul_nonneg hpinv_nn (Real.sqrt_nonneg _)
  have hJensen :
      bernoulliExpectation p
          (fun Omega => Real.sqrt (tangentSamplingDeviation Omega S p + 1))
        ≤ Real.sqrt
            (bernoulliExpectation p
              (fun Omega => tangentSamplingDeviation Omega S p) + 1) := by
    -- write both sides as weighted sums over the (probability) weights.
    have hconc : ConcaveOn ℝ (Set.Ici (0:ℝ)) (Real.sqrt) :=
      Real.strictConcaveOn_sqrt.concaveOn
    have hmap := hconc.le_map_sum
      (t := (Finset.univ : Finset (Finset (Fin n₁ × Fin n₂))))
      (w := bernoulliObservationWeight p)
      (p := fun Omega => tangentSamplingDeviation Omega S p + 1)
      (fun i _ => hw0 i) hw1
      (fun i _ => Set.mem_Ici.mpr (by linarith [hZnn i]))
    -- LHS of hmap = 𝔼[√(Z+1)]; RHS = √(∑ w·(Z+1)) = √(𝔼[Z] + 1).
    have hsum_split :
        (∑ i : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p i *
              (tangentSamplingDeviation i S p + 1))
          = bernoulliExpectation p
              (fun Omega => tangentSamplingDeviation Omega S p) + 1 := by
      unfold bernoulliExpectation
      have hcongr :
          (∑ i : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p i *
                (tangentSamplingDeviation i S p + 1))
            = ∑ i : Finset (Fin n₁ × Fin n₂),
                (bernoulliObservationWeight p i * tangentSamplingDeviation i S p
                  + bernoulliObservationWeight p i) :=
        Finset.sum_congr rfl (fun i _ => by ring)
      rw [hcongr, Finset.sum_add_distrib, hw1]
    calc bernoulliExpectation p
            (fun Omega => Real.sqrt (tangentSamplingDeviation Omega S p + 1))
        = ∑ i : Finset (Fin n₁ × Fin n₂),
            bernoulliObservationWeight p i *
              Real.sqrt (tangentSamplingDeviation i S p + 1) := by
          unfold bernoulliExpectation; rfl
      _ ≤ Real.sqrt
            (∑ i : Finset (Fin n₁ × Fin n₂),
              bernoulliObservationWeight p i *
                (tangentSamplingDeviation i S p + 1)) := by
          simpa using hmap
      _ = Real.sqrt
            (bernoulliExpectation p
              (fun Omega => tangentSamplingDeviation Omega S p) + 1) := by
          rw [hsum_split]
  -- ===== chain: D ≤ pref·𝔼[√(p⁻¹‖G‖)] ≤ pref·√(EZ+1). =====
  calc bernoulliExpectation p
          (fun Omega =>
            p⁻¹ *
            ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
              (∑ ab : Fin n₁ × Fin n₂,
                (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
                  Matrix.vecMulVec
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                    (fun e : Fin n₁ × Fin n₂ =>
                      tangentProjection S (coordinateMatrix ab.1 ab.2)
                        e.1 e.2)))))‖)
      ≤ pref *
          bernoulliExpectation p
            (fun Omega => Real.sqrt (p⁻¹ * GnormOf Omega)) := hstepB
    _ ≤ pref *
          bernoulliExpectation p
            (fun Omega => Real.sqrt (tangentSamplingDeviation Omega S p + 1)) :=
        mul_le_mul_of_nonneg_left hExpMono hpref_nn
    _ ≤ pref *
          Real.sqrt
            (bernoulliExpectation p
              (fun Omega => tangentSamplingDeviation Omega S p) + 1) :=
        mul_le_mul_of_nonneg_left hJensen hpref_nn

#print axioms solution
