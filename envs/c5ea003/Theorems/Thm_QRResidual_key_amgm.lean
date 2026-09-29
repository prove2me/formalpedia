-- Prove2me | Theorems.Thm_QRResidual_key_amgm
-- name    : QRResidual.key_amgm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:50:30.292173+00:00
-- url     : https://prove2.me/theorems/2008eae7-a058-47c5-bee3-f7fa34cea9e6
-- title:
--   Scalar core of the ceiling.
-- statement:
--   **Scalar core of the ceiling.**  If `D² ≤ a S` with `a, S ≥ 0` and `λ > 0`, then
--   `2D ≤ λa + S/λ`.  Applied with `a = ‖c‖²`, `S = Σⱼ⟨r,vⱼ⟩²` this is exactly the statement
--   that no coefficient vector can extract more than `S/λ`.
--
--   ```lean
--   theorem QRResidual.key_amgm{lam a S D : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hS : 0 ≤ S)
--       (hD : D ^ 2 ≤ a * S) : 2 * D ≤ lam * a + S / lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/QRResidual/BlockCeiling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/QRResidual/BlockCeiling.lean#L120

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

theorem QRResidual.key_amgm{lam a S D : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hS : 0 ≤ S)
    (hD : D ^ 2 ≤ a * S) : 2 * D ≤ lam * a + S / lam := by sorry
