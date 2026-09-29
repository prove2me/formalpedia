-- Prove2me | solution 2 for quadratic_neumann_last_index_distinct_response_operator_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-01T10:20:23.087102+00:00
-- url     : https://prove2.me/submissions/8b0b3e2e-a4ec-4940-b957-970526026ec1

import Theorems.Thm_off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
import Theorems.Thm_tangent_projection_spectral_norm_le_universal_multiple
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_le_universal_multiple
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_bound_min_dim
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

open scoped Matrix.Norms.L2Operator

open MatrixCompletion

/-!
# Corrected (rectangular `min`-denominator) Lemma 6.4 response-operator bound.

Target (immutable):
`spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X)
   ≤ Cresp * μ₀ * (r / min) * spectralNorm X`.

This is the SOUND `r/min` replacement for the disproved `r/max` node
`quadratic_neumann_last_index_distinct_response_operator_bound` (3cd3acbe).
The disproof of 3cd3acbe used a single-entry counterexample on a thin `2 × N`
matrix that forces the true scale to be `r/min`, not `r/max`
(CR2009 eqs (4.7)–(4.8); the §6 rectangular convention "replace n with
min(n₁,n₂)").

## Route

The last-index off-diagonal response is exactly the diagonal tangent multiplier
applied to the off-diagonal tangent response:
`quadraticLastIndexDistinctOffDiagonalResponse S X
   = tangentDiagonalMultiplier S (offDiagonalTangentResponse S X)`.

Indeed, at output cell `w1`,
`Z_{w1} = ∑_{w3 ≠ w1} X_{w3} · K(w3, w1) · Kdiag(w1)
        = Kdiag(w1) · (∑_{w3 ≠ w1} X_{w3} · K(w3, w1))
        = Kdiag(w1) · (offDiagonalTangentResponse S X)_{w1}`,
which is `tangentDiagonalMultiplier` (the entrywise `Kdiag` weight) of
`offDiagonalTangentResponse S X`.

Hence, chaining the Lemma-6.4-style spectral bounds (all imported children are
Proved on the platform):
* `‖tangentDiagonalMultiplier S Y‖ ≤ Cdiag · (μ₀ r/min) · ‖Y‖`
  (`tangent_diagonal_multiplier_spectral_norm_bound_min_dim`, 47ac7371, Proved),
* the universal off-diagonal-response bound `‖offResp X‖ ≤ Cresp₀ · ‖X‖`, proven
  INLINE from the Proved identity `offResp = P_T X − tangentDiagMult X`
  (`off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier`),
  the Proved `‖P_T X‖ ≤ Ctan · ‖X‖`
  (`tangent_projection_spectral_norm_le_universal_multiple`), and the Proved
  universal diagonal multiplier bound
  (`tangent_diagonal_multiplier_spectral_norm_le_universal_multiple`).

We obtain `‖Z‖ ≤ Cdiag · (μ₀ r/min) · Cresp₀ · ‖X‖`, i.e. the `r/min` bound with
`Cresp = Cdiag · Cresp₀`.

Source: Candès–Recht 2008, §6.3, Lemma 6.4 (p. 30).
-/

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

private lemma spectralNorm_sub_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X - Y) ≤ spectralNorm X + spectralNorm Y := by
  rw [spectralNorm_eq_l2_opNorm, spectralNorm_eq_l2_opNorm, spectralNorm_eq_l2_opNorm]
  exact norm_sub_le _ _

/-- The last-index off-diagonal response is the diagonal tangent multiplier of
the off-diagonal tangent response. -/
private lemma last_response_eq_diag_of_offdiag
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    quadraticLastIndexDistinctOffDiagonalResponse S X =
      tangentDiagonalMultiplier S (offDiagonalTangentResponse S X) := by
  ext i j
  -- RHS = (offResp X)_{ij} · Kdiag(ij).
  rw [tangentDiagonalMultiplier, offDiagonalTangentResponse]
  -- LHS: entry (i,j) of the double-sum-of-scaled-coordinateMatrix.
  rw [quadraticLastIndexDistinctOffDiagonalResponse, Matrix.sum_apply]
  -- outer sum over w1 collapses to w1 = (i,j)
  rw [Finset.sum_eq_single (i, j)]
  · -- at w1 = (i,j): coordinateMatrix (i,j) evaluated at (i,j) = 1
    rw [Matrix.sum_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun w3 _ => ?_)
    by_cases hw : w3 = ((i, j) : Fin n₁ × Fin n₂)
    · subst hw; simp
    · rw [if_neg (by exact fun h => hw h.symm), if_neg (by simpa using hw)]
      simp only [Matrix.smul_apply, coordinateMatrix, smul_eq_mul, and_self,
        if_true, mul_one]
  · -- w1 ≠ (i,j): every summand's coordinateMatrix w1 is 0 at (i,j)
    intro w1 _ hw1
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro w3 _
    by_cases h : w1 = w3
    · simp [h]
    · rw [if_neg h]
      simp only [Matrix.smul_apply, coordinateMatrix, smul_eq_mul]
      rw [if_neg (by
        rintro ⟨h1, h2⟩
        exact hw1 (Prod.ext (by simpa using h1.symm) (by simpa using h2.symm)))]
      ring
  · intro hcontra
    exact (hcontra (Finset.mem_univ _)).elim

theorem solution :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (quadraticLastIndexDistinctOffDiagonalResponse S X) ≤
            Cresp * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) * spectralNorm X := by
  obtain ⟨Ctan, hCtan, hTan⟩ := tangent_projection_spectral_norm_le_universal_multiple
  obtain ⟨CdiagU, hCdiagU, hDiagU⟩ :=
    tangent_diagonal_multiplier_spectral_norm_le_universal_multiple
  obtain ⟨Cdiag, hCdiag, hDiag⟩ := tangent_diagonal_multiplier_spectral_norm_bound_min_dim
  refine ⟨Cdiag * (Ctan + CdiagU), by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 X
  have hμ₀0 : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hmin_pos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  -- rewrite the response as diag-multiplier of off-diagonal response
  rw [last_response_eq_diag_of_offdiag S X]
  -- universal bound on the off-diagonal tangent response:
  -- ‖offResp X‖ ≤ (Ctan + CdiagU)·‖X‖
  have hXnn : 0 ≤ spectralNorm X := norm_nonneg _
  have hoffbound :
      spectralNorm (offDiagonalTangentResponse S X) ≤ (Ctan + CdiagU) * spectralNorm X := by
    rw [off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier S X]
    calc
      spectralNorm (tangentProjection S X - tangentDiagonalMultiplier S X)
          ≤ spectralNorm (tangentProjection S X) +
              spectralNorm (tangentDiagonalMultiplier S X) := spectralNorm_sub_le _ _
      _ ≤ Ctan * spectralNorm X + CdiagU * spectralNorm X :=
            add_le_add (hTan n₁ n₂ r M S X)
              (hDiagU n₁ n₂ r M μ₀ S X hn₁ hn₂ hr hμ₀ hA0)
      _ = (Ctan + CdiagU) * spectralNorm X := by ring
  -- ‖diagMult(offResp X)‖ ≤ Cdiag·(μ₀r/min)·‖offResp X‖
  have h1 :
      spectralNorm (tangentDiagonalMultiplier S (offDiagonalTangentResponse S X)) ≤
        Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
          spectralNorm (offDiagonalTangentResponse S X) :=
    hDiag n₁ n₂ r M μ₀ S (offDiagonalTangentResponse S X) hn₁ hn₂ hr hμ₀ hA0
  have hcoef_nonneg : 0 ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by positivity
  calc
    spectralNorm (tangentDiagonalMultiplier S (offDiagonalTangentResponse S X))
        ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
            spectralNorm (offDiagonalTangentResponse S X) := h1
    _ ≤ Cdiag * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) * ((Ctan + CdiagU) * spectralNorm X) :=
          mul_le_mul_of_nonneg_left hoffbound hcoef_nonneg
    _ = (Cdiag * (Ctan + CdiagU)) * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) * spectralNorm X := by
          ring
