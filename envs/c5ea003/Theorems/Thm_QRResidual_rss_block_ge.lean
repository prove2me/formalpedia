-- Prove2me | Theorems.Thm_QRResidual_rss_block_ge
-- name    : QRResidual.rss_block_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:51:31.64635+00:00
-- url     : https://prove2.me/theorems/9b351612-3a36-4cf8-8fc6-2861b53e37f9
-- title:
--   The block ceiling (RSS form).
-- statement:
--   **The block ceiling (RSS form).**  Under a lower frame bound `λ`, no linear
--   combination of the block removes more than `(Σⱼ⟨r,vⱼ⟩²)/λ` of the residual energy of the
--   baseline `g`.
--
--   ```lean
--   theorem QRResidual.rss_block_ge{lam : ℝ} (hlam : 0 < lam) {v : Fin k → (ι → ℝ)}
--       (hframe : FrameLower lam v) (y g : ι → ℝ) :
--       sqNorm (y - g) - (∑ j, (dot (y - g) (v j)) ^ 2) / lam ≤ rss y (blockClass g v) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/QRResidual/BlockCeiling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/QRResidual/BlockCeiling.lean#L144

-- Thm stub generated from MachineLearning/QRResidual/BlockCeiling.lean
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

theorem QRResidual.rss_block_ge{lam : ℝ} (hlam : 0 < lam) {v : Fin k → (ι → ℝ)}
    (hframe : FrameLower lam v) (y g : ι → ℝ) :
    sqNorm (y - g) - (∑ j, (dot (y - g) (v j)) ^ 2) / lam ≤ rss y (blockClass g v) := by sorry
