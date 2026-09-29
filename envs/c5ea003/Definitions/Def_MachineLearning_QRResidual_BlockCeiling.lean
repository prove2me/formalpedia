-- Prove2me | Definitions.Def_MachineLearning_QRResidual_BlockCeiling
-- name    : MachineLearning_QRResidual_BlockCeiling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:55:11.581453+00:00
-- url     : https://prove2.me/theorems/a0832a7f-aa8e-41e0-8193-a66f640c79ac
-- title:
--   Aether Catalog definitions — MachineLearning_QRResidual_BlockCeiling
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.QRResidual.BlockCeiling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/QRResidual/BlockCeiling.lean by skeleton subtraction
import Mathlib
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

namespace QRResidual

open Finset

variable {ι : Type*} [Fintype ι] {k : ℕ}

/-! ## Elementary bilinear algebra of the sample inner product -/




/-! ## The linear span of a block of covariates -/

/-- The prediction contributed by the block `v` with coefficient vector `c`. -/
def blockSpan (v : Fin k → (ι → ℝ)) (c : Fin k → ℝ) : ι → ℝ := ∑ j, c j • v j


/-- The model class obtained by augmenting the baseline `g` with the whole block. -/
def blockClass (g : ι → ℝ) (v : Fin k → (ι → ℝ)) : Set (ι → ℝ) :=
  {h : ι → ℝ | ∃ c : Fin k → ℝ, h = g + blockSpan v c}

/-- A **lower frame bound** for the block: the design matrix is not arbitrarily
ill-conditioned.  For an orthonormal block one may take `λ = 1`; in general `λ` is the
smallest eigenvalue of the Gram matrix. -/
def FrameLower (lam : ℝ) (v : Fin k → (ι → ℝ)) : Prop :=
  ∀ c : Fin k → ℝ, lam * ∑ j, (c j) ^ 2 ≤ sqNorm (blockSpan v c)





/-! ## The scalar core: an AM–GM step -/


/-! ## The block ceiling -/





/-! ## The exact dichotomy for a block -/



/-! ## Conditional dominance: the block cannot absorb an orthogonal feature -/

/-- The model class obtained by augmenting the block class further by one feature `w`. -/
def blockClassPlus (g : ι → ℝ) (v : Fin k → (ι → ℝ)) (w : ι → ℝ) : Set (ι → ℝ) :=
  {h : ι → ℝ | ∃ (c : Fin k → ℝ) (t : ℝ), h = g + blockSpan v c + t • w}



/-! ## The asymmetry capstone -/


end QRResidual


