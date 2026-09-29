-- Prove2me | solution 1 for spectral_norm_le_singular_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T14:06:39.134075+00:00
-- url     : https://prove2.me/submissions/0d5cf43e-a434-4b73-85c2-8bd6de80fdeb

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion Module InnerProductSpace LinearMap

/-- Real inner product on Euclidean space as a coordinate sum. -/
private theorem inner_euclid_sum {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ u v : ℝ) = ∑ i, u i * v i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (RCLike.inner_apply (u i) (v i)).trans (by rw [starRingEnd_apply, star_trivial]; ring)

/-- Rayleigh bound: for a symmetric operator `S` on a nontrivial finite-dimensional
real inner product space, `⟪S x, x⟫ ≤ λ_0 ‖x‖²` where `λ_0` is the top eigenvalue. -/
private theorem rayleigh_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric)
    (n : ℕ) (hn : Module.finrank ℝ E = n) (hn0 : 0 < n) (x : E) :
    (inner ℝ (S x) x : ℝ) ≤ hS.eigenvalues hn ⟨0, hn0⟩ * ‖x‖^2 := by
  set b := hS.eigenvectorBasis hn with hb
  have hiso : (inner ℝ (S x) x : ℝ) = (inner ℝ (b.repr (S x)) (b.repr x) : ℝ) :=
    (b.repr.inner_map_map (S x) x).symm
  rw [hiso, inner_euclid_sum]
  have key : ∀ i, b.repr (S x) i = hS.eigenvalues hn i * b.repr x i :=
    fun i => hS.eigenvectorBasis_apply_self_apply hn x i
  have hsum : (∑ i, b.repr (S x) i * b.repr x i)
      = ∑ i, hS.eigenvalues hn i * (b.repr x i)^2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [key i]; ring
  rw [hsum]
  have hbound : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      hS.eigenvalues hn i * (b.repr x i)^2
        ≤ hS.eigenvalues hn ⟨0, hn0⟩ * (b.repr x i)^2 := by
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact hS.eigenvalues_antitone hn (Nat.zero_le _)
  calc ∑ i, hS.eigenvalues hn i * (b.repr x i)^2
      ≤ ∑ i, hS.eigenvalues hn ⟨0, hn0⟩ * (b.repr x i)^2 := Finset.sum_le_sum hbound
    _ = hS.eigenvalues hn ⟨0, hn0⟩ * ∑ i, (b.repr x i)^2 := by rw [Finset.mul_sum]
    _ = hS.eigenvalues hn ⟨0, hn0⟩ * ‖x‖^2 := by
        congr 1
        rw [← b.repr.norm_map x, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Real.norm_eq_abs, sq_abs]

theorem solution :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm Y ≤ (Matrix.toEuclideanLin Y).singularValues 0 := by
  intro n₁ n₂ Y
  set T := Matrix.toEuclideanLin Y with hT
  set σ₀ := T.singularValues 0 with hσ₀
  have hσ₀_nonneg : 0 ≤ σ₀ := T.singularValues_nonneg 0
  -- spectralNorm Y = ‖toContinuousLinearMap T‖
  show ‖(LinearMap.toContinuousLinearMap T)‖ ≤ σ₀
  apply ContinuousLinearMap.opNorm_le_bound _ hσ₀_nonneg
  intro x
  rw [show (LinearMap.toContinuousLinearMap T) x = T x from rfl]
  -- Reduce to ‖T x‖² ≤ σ₀² ‖x‖² ; both sides nonneg.
  have hnorm_sq : ‖T x‖^2 ≤ σ₀^2 * ‖x‖^2 := by
    rcases Nat.eq_zero_or_pos n₂ with hn2 | hn2
    · -- domain trivial: T x = 0
      subst hn2
      have hx : x = 0 := Subsingleton.elim _ _
      simp [hx]
    · -- ‖T x‖² = ⟪S x, x⟫ where S = adjoint T ∘ₗ T
      set S := (LinearMap.adjoint T) ∘ₗ T with hS_def
      have hSsym : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
      have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n₂)) = n₂ := by simp
      -- ‖T x‖² = ⟪S x, x⟫
      have hnormeq : ‖T x‖^2 = (inner ℝ (S x) x : ℝ) := by
        have h1 : (inner ℝ (S x) x : ℝ) = (inner ℝ (T x) (T x) : ℝ) := by
          rw [hS_def]
          simp only [LinearMap.comp_apply]
          exact LinearMap.adjoint_inner_left T x (T x)
        rw [h1, real_inner_self_eq_norm_sq]
      rw [hnormeq]
      -- Rayleigh: ⟪S x,x⟫ ≤ λ_0 ‖x‖² with λ_0 = σ₀²
      have hray := rayleigh_le S hSsym n₂ hfr hn2 x
      -- λ_0 = σ₀²
      have hlam : hSsym.eigenvalues hfr ⟨0, hn2⟩ = σ₀^2 := by
        have hsq := T.sq_singularValues_fin hfr ⟨0, hn2⟩
        simpa [hσ₀] using hsq.symm
      rw [hlam] at hray
      exact hray
  -- from ‖Tx‖² ≤ σ₀²‖x‖² = (σ₀‖x‖)² conclude ‖Tx‖ ≤ σ₀‖x‖
  have hrhs : σ₀^2 * ‖x‖^2 = (σ₀ * ‖x‖)^2 := by ring
  rw [hrhs] at hnorm_sq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hσ₀_nonneg (norm_nonneg _))).mp hnorm_sq
