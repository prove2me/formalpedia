-- Prove2me | solution 1 for QRResidual.rss_block_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:24:53.890011+00:00
-- url     : https://prove2.me/submissions/0aade8cd-fa1b-45a7-b65c-7401bf1750c9

-- Sol generated from MachineLearning/QRResidual/BlockCeiling.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_key_amgm
import Theorems.Thm_QRResidual_le_rss

/-!
# Ceilings for a block of covariates: how to certify a null result

`ResidualLift` supplies the *positive* half of feature-augmentation theory: a feature that
correlates with the residual of a baseline fit provably lifts `R²`.  Experiment 585 needs
the *negative* half.  There a block of four "neighbour smoothness" covariates
`[ω(N−1), ω(N+1), log lpf(N−1), log lpf(N+1)]` was appended to a baseline built from the
quadratic-residue footprint dial, and the observed incremental `R²` was
`ΔR² = 0.4307 − 0.4112 = 0.01946`, with best single residual correlation `|r| = 0.16`.
The pre-registered null was `ΔR² < 0.02`.

An observed small `ΔR²` is, by itself, only a measurement.  What turns it into a *bound*
is a theorem of the form "with these correlations and this design conditioning, no
`ΔR²` larger than … is possible".  That is what this file proves.

Main results.

* `key_amgm` — the scalar AM–GM step `2D ≤ λa + S/λ` from `D² ≤ aS`.
* `rss_block_ge` — **the block ceiling.**  If the block `v : Fin k → (ι → ℝ)` satisfies a
  lower frame bound `λ‖c‖² ≤ ‖Σ cⱼvⱼ‖²`, then *no* linear combination of the block can
  remove more than `(Σⱼ⟨r,vⱼ⟩²)/λ` of the residual energy.
* `rsq_block_le`, `rsq_block_le_of_corr` — the `R²` form, and the quotable certificate
  `ΔR² ≤ k ρ² (1 − R²₀)/λ` for a unit-normalised block whose residual correlations are all
  at most `ρ`.
* `block_lift_iff_exists_corr` — the exact dichotomy: a block lifts `R²` **iff** at least
  one of its features correlates with the baseline residual.
* `rss_blockPlus_le`, `rsq_blockPlus_ge` — **conditional dominance.**  A feature orthogonal
  to the block keeps its entire individual lift after the block has been fitted; the block
  cannot absorb it.
* `lift_asymmetry` — the capstone: under a correlation ceiling on the block and a lift
  floor on the dial, the dial's incremental value *given the block* strictly exceeds the
  block's incremental value *given the baseline*.  This is the formal shape of the
  experiment's verdict "nothing beyond the dial".
-/

open QRResidual

open Finset

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-! ## Elementary bilinear algebra of the sample inner product -/

/-- Expansion of the residual energy after subtracting an arbitrary correction. -/
theorem sqNorm_sub (r u : ι → ℝ) : sqNorm (r - u) = sqNorm r - 2 * dot r u + sqNorm u := by
  simp only [sqNorm, dot, Pi.sub_apply]
  have h : ∀ i : ι, (r i - u i) ^ 2 = (r i) ^ 2 - 2 * (r i * u i) + (u i) ^ 2 := by
    intro i; ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]



/-! ## The linear span of a block of covariates -/


omit [Fintype ι] in
theorem blockSpan_apply (v : Fin k → (ι → ℝ)) (c : Fin k → ℝ) (i : ι) :
    blockSpan v c i = ∑ j, c j * v j i := by
  simp [blockSpan, Finset.sum_apply]



theorem dot_blockSpan (r : ι → ℝ) (v : Fin k → (ι → ℝ)) (c : Fin k → ℝ) :
    dot r (blockSpan v c) = ∑ j, c j * dot r (v j) := by
  simp only [dot, blockSpan_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact Finset.sum_congr rfl fun i _ => by ring




/-! ## The scalar core: an AM–GM step -/


/-! ## The block ceiling -/





/-! ## The exact dichotomy for a block -/



/-! ## Conditional dominance: the block cannot absorb an orthogonal feature -/




/-! ## The asymmetry capstone -/



open QRResidual in
theorem solution{lam : ℝ} (hlam : 0 < lam) {v : Fin k → (ι → ℝ)}
    (hframe : FrameLower lam v) (y g : ι → ℝ) :
    sqNorm (y - g) - (∑ j, (dot (y - g) (v j)) ^ 2) / lam ≤ rss y (blockClass g v) := by
  refine le_rss ⟨g + blockSpan v 0, ⟨0, rfl⟩⟩ ?_
  rintro h ⟨c, rfl⟩
  have hrw : y - (g + blockSpan v c) = (y - g) - blockSpan v c := by
    funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
  have hexp : sqNorm ((y - g) - blockSpan v c)
      = sqNorm (y - g) - 2 * dot (y - g) (blockSpan v c) + sqNorm (blockSpan v c) :=
    sqNorm_sub _ _
  rw [hrw, hexp]
  set a : ℝ := ∑ j, (c j) ^ 2 with ha'
  set S : ℝ := ∑ j, (dot (y - g) (v j)) ^ 2 with hS'
  set D : ℝ := dot (y - g) (blockSpan v c) with hD'
  have hcs : D ^ 2 ≤ a * S := by
    rw [hD', dot_blockSpan]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have haa : 0 ≤ a := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hfr : lam * a ≤ sqNorm (blockSpan v c) := hframe c
  have := key_amgm hlam haa hSS hcs
  linarith
