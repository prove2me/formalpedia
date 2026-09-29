-- Prove2me | solution 1 for QRResidual.rsq_block_le_of_corr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:30.943676+00:00
-- url     : https://prove2.me/submissions/647efb90-d6c0-49f4-8ab4-b5581d4f5359

-- Sol generated from MachineLearning/QRResidual/BlockCeiling.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_rss_block_ge
import Theorems.Thm_QRResidual_sqNorm_residual_eq

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


/-- **The block ceiling (`R²` form).** -/
theorem rsq_block_le {lam : ℝ} (hlam : 0 < lam) {v : Fin k → (ι → ℝ)}
    (hframe : FrameLower lam v) (y g : ι → ℝ) (htss : 0 < tss y) :
    rsq y (blockClass g v)
      ≤ rsqOf y g + (∑ j, (dot (y - g) (v j)) ^ 2) / (lam * tss y) := by
  have h := rss_block_ge hlam hframe y g
  have hdiv := (div_le_div_iff_of_pos_right htss).2 h
  have hsplit : (sqNorm (y - g) - (∑ j, (dot (y - g) (v j)) ^ 2) / lam) / tss y
      = sqNorm (y - g) / tss y - (∑ j, (dot (y - g) (v j)) ^ 2) / (lam * tss y) := by
    field_simp
  rw [hsplit] at hdiv
  unfold rsq rsqOf
  linarith



/-! ## The exact dichotomy for a block -/



/-! ## Conditional dominance: the block cannot absorb an orthogonal feature -/




/-! ## The asymmetry capstone -/



open QRResidual in
theorem solution{lam rho : ℝ} (hlam : 0 < lam) {v : Fin k → (ι → ℝ)}
    (hframe : FrameLower lam v) (y g : ι → ℝ) (htss : 0 < tss y)
    (hcorr : ∀ j, (dot (y - g) (v j)) ^ 2 ≤ rho ^ 2 * sqNorm (y - g)) :
    rsq y (blockClass g v) - rsqOf y g ≤ k * rho ^ 2 * (1 - rsqOf y g) / lam := by
  have hceil := rsq_block_le hlam hframe y g htss
  have hsum : (∑ j, (dot (y - g) (v j)) ^ 2) ≤ k * (rho ^ 2 * sqNorm (y - g)) := by
    calc (∑ j, (dot (y - g) (v j)) ^ 2)
        ≤ ∑ _j : Fin k, rho ^ 2 * sqNorm (y - g) :=
          Finset.sum_le_sum fun j _ => hcorr j
      _ = k * (rho ^ 2 * sqNorm (y - g)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hr := sqNorm_residual_eq (y := y) (g := g) htss
  have hstep : (∑ j, (dot (y - g) (v j)) ^ 2) / (lam * tss y)
      ≤ k * rho ^ 2 * (1 - rsqOf y g) / lam := by
    rw [div_le_div_iff₀ (by positivity) hlam]
    have h2 : (k : ℝ) * rho ^ 2 * (1 - rsqOf y g) * (lam * tss y)
        = lam * ((k : ℝ) * (rho ^ 2 * ((1 - rsqOf y g) * tss y))) := by ring
    rw [h2, ← hr]
    have : (∑ j, (dot (y - g) (v j)) ^ 2) * lam
        ≤ (k * (rho ^ 2 * sqNorm (y - g))) * lam :=
      mul_le_mul_of_nonneg_right hsum hlam.le
    nlinarith [this]
  linarith
