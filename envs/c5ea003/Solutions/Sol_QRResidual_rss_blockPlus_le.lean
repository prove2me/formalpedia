-- Prove2me | solution 1 for QRResidual.rss_blockPlus_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:31.51357+00:00
-- url     : https://prove2.me/submissions/0ab33339-cd8f-45d6-9984-8b6a8af9e8a6

-- Sol generated from MachineLearning/QRResidual/BlockCeiling.lean
import Mathlib
import Definitions.Def_MachineLearning_QRResidual_BlockCeiling
import Definitions.Def_MachineLearning_QRResidual_ResidualLift
import Theorems.Thm_QRResidual_rss_le_of_mem
import Theorems.Thm_QRResidual_sqNorm_sub_smul_eq

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


theorem dot_sub_left (r u w : ι → ℝ) : dot (r - u) w = dot r w - dot u w := by
  simp only [dot, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_comm (u w : ι → ℝ) : dot u w = dot w u := by
  simp only [dot]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

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
theorem solution{v : Fin k → (ι → ℝ)} {w : ι → ℝ} (hw : sqNorm w ≠ 0)
    (horth : ∀ j, dot (v j) w = 0) (y g : ι → ℝ) :
    rss y (blockClassPlus g v w)
      ≤ rss y (blockClass g v) - (dot (y - g) w) ^ 2 / sqNorm w := by
  set r := y - g with hr
  set L : ℝ := (dot r w) ^ 2 / sqNorm w with hL
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  -- pick a nearly optimal coefficient vector for the block
  obtain ⟨b, hbmem, hblt⟩ :
      ∃ b ∈ (fun h => sqNorm (y - h)) '' blockClass g v, b < rss y (blockClass g v) + ε := by
    have hne : ((fun h => sqNorm (y - h)) '' blockClass g v).Nonempty :=
      ⟨sqNorm (y - (g + blockSpan v 0)), ⟨_, ⟨0, rfl⟩, rfl⟩⟩
    exact exists_lt_of_csInf_lt hne (by linarith : rss y (blockClass g v)
      < rss y (blockClass g v) + ε)
  obtain ⟨h, ⟨c, rfl⟩, rfl⟩ := hbmem
  have hspan : y - (g + blockSpan v c) = r - blockSpan v c := by
    funext i; simp only [hr, Pi.sub_apply, Pi.add_apply]; ring
  -- the residual after the block still has the same correlation with `w`
  have hdotu : dot (blockSpan v c) w = 0 := by
    have : dot (blockSpan v c) w = ∑ j, c j * dot (v j) w := by
      rw [dot_comm, dot_blockSpan]
      exact Finset.sum_congr rfl fun j _ => by rw [dot_comm]
    rw [this]
    exact Finset.sum_eq_zero fun j _ => by rw [horth j]; ring
  have hdotr : dot (r - blockSpan v c) w = dot r w := by
    rw [dot_sub_left, hdotu, sub_zero]
  set t : ℝ := dot (r - blockSpan v c) w / sqNorm w with ht
  have hmem : g + blockSpan v c + t • w ∈ blockClassPlus g v w := ⟨c, t, rfl⟩
  have hrw2 : y - (g + blockSpan v c + t • w) = (r - blockSpan v c) - t • w := by
    funext i; simp only [hr, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hcalc : sqNorm (y - (g + blockSpan v c + t • w))
      = sqNorm (r - blockSpan v c) - (dot (r - blockSpan v c) w) ^ 2 / sqNorm w := by
    rw [hrw2, ht]
    exact sqNorm_sub_smul_eq _ _ hw
  have hstep : rss y (blockClassPlus g v w)
      ≤ sqNorm (r - blockSpan v c) - L := by
    have := rss_le_of_mem (y := y) hmem
    rw [hcalc, hdotr] at this
    exact this
  have : sqNorm (r - blockSpan v c) = sqNorm (y - (g + blockSpan v c)) := by rw [hspan]
  linarith [hstep, hblt, this]
