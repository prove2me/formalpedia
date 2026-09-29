-- Prove2me | solution 1 for QRResidual.key_amgm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:12:36.503846+00:00
-- url     : https://prove2.me/submissions/5cb426d2-1c7f-4716-b014-b9864cfaea3d

-- Sol generated from MachineLearning/QRResidual/BlockCeiling.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_ResidualLift

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




/-! ## The linear span of a block of covariates -/









/-! ## The scalar core: an AM–GM step -/


/-! ## The block ceiling -/





/-! ## The exact dichotomy for a block -/



/-! ## Conditional dominance: the block cannot absorb an orthogonal feature -/




/-! ## The asymmetry capstone -/



open QRResidual in
theorem solution{lam a S D : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hS : 0 ≤ S)
    (hD : D ^ 2 ≤ a * S) : 2 * D ≤ lam * a + S / lam := by
  rcases le_or_gt D 0 with hD0 | hD0
  · have h1 : 0 ≤ lam * a := mul_nonneg hlam.le ha
    have h2 : 0 ≤ S / lam := div_nonneg hS hlam.le
    linarith
  · have hmul : 4 * lam ^ 2 * D ^ 2 ≤ 4 * lam ^ 2 * (a * S) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h1 : (2 * lam * D) ^ 2 ≤ (lam ^ 2 * a + S) ^ 2 := by
      nlinarith [sq_nonneg (lam ^ 2 * a - S)]
    have h2 : (0 : ℝ) ≤ lam ^ 2 * a + S := by positivity
    have h3 : (0 : ℝ) ≤ 2 * lam * D := by positivity
    have h4 : 2 * lam * D ≤ lam ^ 2 * a + S := by nlinarith [h1, h2, h3]
    have heq : lam * a + S / lam - 2 * D = (lam ^ 2 * a + S - 2 * lam * D) / lam := by
      field_simp
    have h5 : 0 ≤ (lam ^ 2 * a + S - 2 * lam * D) / lam :=
      div_nonneg (by linarith) hlam.le
    linarith [heq ▸ h5]
