-- Prove2me | solution 1 for talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-25T02:37:37.833589+00:00
-- url     : https://prove2.me/submissions/4261ca7a-6774-4925-8598-7a29d379ed34

import Definitions.Def_matrix_completion_talagrand
import Theorems.Thm_talagrand_tangent_sampling_upper_tail_bound_dense
import Theorems.Thm_tangent_deviation_bound_prob_from_two_sided_tail

open MatrixCompletion

/-
REDUCTION of e5bb2914_dense `talagrand_tangent_sampling_deviation_from_increment_variance_bounds_dense`
(with density m ≥ β·μ₀·max·r·log max) to two children:
  (bridge) fa14091c `tangent_deviation_bound_prob_from_two_sided_tail` (PROVED), and
  (C2_dense) `talagrand_tangent_sampling_upper_tail_bound_dense`         (the genuine Open core, density now threaded).

Identical to the non-dense Sol_e5bb2914_reduction except the density hypothesis is intro'd and PASSED to
C2_dense (whose conclusion is the two-sided Talagrand–Bennett tail; with density it closes, CR Thm 9.1 eq(9.2)).
The reduction's OWN body is sorry-free; only the imported stubs carry sorry.

`theorem solution` is TOP-LEVEL per platform rule.
-/

theorem solution
    (Cexpect : ℝ) :
    0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        TangentSamplingTalagrandIncrementBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        TangentSamplingTalagrandVarianceBound S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              tangentSamplingDeviation Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              TangentSamplingDeviationBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m +
                  tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m)) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCexpect
  obtain ⟨Ctail, c, hCtail0, hc0, hC2⟩ :=
    talagrand_tangent_sampling_upper_tail_bound_dense Cexpect hCexpect
  refine ⟨Ctail, c, hCtail0, hc0, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hdens hInc hVar hEZ
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set t : ℝ := tangentSamplingDeviationScale Ctail β μ₀ (max n₁ n₂) r m with ht
  set q : ℝ := c * Real.rpow (↑(max n₁ n₂)) (-β) with hq
  set Se : ℝ := tangentSamplingDeviationScale Cexpect β μ₀ (max n₁ n₂) r m with hSe
  set EZ : ℝ :=
    bernoulliExpectation p (fun Omega => tangentSamplingDeviation Omega S p) with hEZdef
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hden : (0 : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := mul_pos hn₁R hn₂R
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hden]
    have : ((m : ℝ)) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_mul] at this
    exact this
  have htail :
      bernoulliEventProb p
          (fun Omega => |tangentSamplingDeviation Omega S p - EZ| > t) ≤ q := by
    have := hC2 β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hdens hInc hVar hEZ
    exact this
  have hbudget : EZ + t ≤ Se + t := by
    have : EZ ≤ Se := hEZ
    linarith
  have hbridge :=
    tangent_deviation_bound_prob_from_two_sided_tail (S := S)
      p t q (Se + t) hp0 hp1 htail hbudget
  exact hbridge
