-- Prove2me | solution 1 for AsaiSecondMoment.secondMoment_aligned_order
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:32:00.639754+00:00
-- url     : https://prove2.me/submissions/d5e1ffe8-d0dd-4dab-a477-7fa530415755

-- Sol generated from Novelty/AsaiOverlapMultiplicity.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiOverlapMultiplicity
import Definitions.Def_Novelty_AsaiSecondMoment
import Theorems.Thm_AsaiLargeSieve_largeSieve_of_quasiOrthogonal
import Theorems.Thm_AsaiLargeSieve_lowerBound_of_quasiOrthogonal
import Theorems.Thm_AsaiSecondMoment_afe_eq_linForm_aggregate
import Theorems.Thm_AsaiSecondMoment_quasiOrthogonal_const_nonneg
import Theorems.Thm_AsaiSecondMoment_secondMoment_overlap_le
import Theorems.Thm_AsaiSecondMoment_sum_normSq_aggregate_aligned
/-
# The overlap multiplicity of an approximate functional equation

This file continues the formalisation of the analytic skeleton of the paper
**"On the Second Moment of `L(1/2, As(f) × φ)`"** carried out in `Novelty.AsaiLargeSieve`,
`Novelty.AsaiLargeSieveGram`, `Novelty.AsaiSecondMoment`, `Novelty.AsaiMomentApplications`,
`Novelty.AsaiLargeSieveSharp` and `Novelty.AsaiSecondMomentLower`.  It settles the upper
half of conjecture **C6** of `FUTURE_DIRECTIONS.md`, together with its sharpness.

## What is proved here

The flagship second moment bound `AsaiSecondMoment.secondMoment_uniform` carries a factor
`J²`, where `J` is the number of blocks of the approximate functional equation, and comes
from a blind application of Cauchy–Schwarz over the blocks.  For *spectrally separated*
blocks `AsaiSecondMoment.secondMoment_disjoint_uniform` removes one factor `J`.  Conjecture
C6 asserted that neither `J²` nor `J` is the right parameter: the correct one is the
**overlap multiplicity**

`r = max_{n < N} #{j < J : A j n ≠ 0}`,

i.e. the largest number of blocks that are simultaneously active at a single coefficient.

* `AsaiSecondMoment.OverlapMultiplicity` — the definition.
* `AsaiSecondMoment.sum_normSq_aggregate_le_overlap` — the arithmetic heart: the `ℓ²`-mass
  of the aggregated coefficient vector `n ↦ ∑_j w j · A j n` is at most `r` times the
  weighted sum of the blockwise masses.  (For `r = 1` this is the *equality*
  `sum_normSq_aggregate_of_disjoint`; for `r = J` it is the pointwise Cauchy–Schwarz
  inequality that produces the flagship `J²`.)
* `AsaiSecondMoment.secondMoment_overlap_le` and `secondMoment_overlap_uniform` — the
  resulting second moment bounds `C · r · ∑_j |w j|²‖A j‖²` and `r · J · C · B`.
* `AsaiSecondMoment.secondMoment_overlap_lt_flagship` — whenever `r < J` (and the problem is
  non-degenerate) the new bound is *strictly* stronger than the flagship `J² · C · B`, so
  the exponent `2` on `J` is indeed never correct below the maximal overlap.
* `AsaiSecondMoment.secondMoment_overlap_of_disjoint` — the case `r = 1` recovers exactly the
  spectrally separated bound, so the new statement genuinely interpolates between the two
  previously proved extremes.
* `AsaiSecondMoment.secondMoment_overlap_attained` — an explicit instance with `r = J = 2` in
  which the bound `C · r · ∑_j |w j|²‖A j‖²` holds *with equality*, so the linear dependence
  on `r` cannot be improved.

The last section settles the companion conjecture C9: for *aligned* configurations (the `r`
active blocks carry the same value at each coefficient) the aggregation is lossless
(`sum_normSq_aggregate_aligned`), so Petersson quasi-orthogonality gives a matching lower
bound (`secondMoment_aligned_lower`) and, in the regime `2eN ≤ D`, the exact order
`∑_f |L f|² ≍ D · r · ∑_j ‖A j‖²` for every intermediate overlap `r`
(`secondMoment_aligned_order`).

Everything is proved for an arbitrary finite family of eigenvalue systems
`lam : ι → ℕ → ℂ`, of which the Hecke eigenvalues of the Asai lifts are one instance.
-/

open Finset Complex AsaiLargeSieve

open AsaiSecondMoment

variable {ι : Type*}










/-! ## Conjecture C9: a matching lower bound at intermediate overlap

The upper bound above loses a factor `r`.  Is that loss real for `1 < r < J`, or only an
artefact of the pointwise Cauchy–Schwarz step?  It is real.  The extremal configuration is the
one in which the active blocks are *aligned*: at each coefficient `n` the `r` active blocks
carry the same value `c n`, so nothing cancels in the aggregation and the pointwise
Cauchy–Schwarz step is an equality.  Under Petersson quasi-orthogonality this produces a
lower bound of exactly the same shape as the upper bound, and hence the exact order
`∑_f |L f|² ≍ D · r · ∑_j ‖A j‖²` for every `r`. -/


/-- An aligned configuration with active sets of size `r` has overlap multiplicity `r`. -/
theorem overlapMultiplicity_of_aligned (N J r : ℕ) (A : ℕ → ℕ → ℂ) (act : ℕ → Finset ℕ)
    (c : ℕ → ℂ) (hal : AlignedOverlap N J A act c)
    (hcard : ∀ n ∈ Finset.range N, (act n).card ≤ r) :
    OverlapMultiplicity N J A r := by
  classical
  intro n hn
  obtain ⟨_, hval⟩ := hal n hn
  have hsub : (Finset.range J).filter (fun j => A j n ≠ 0) ⊆ act n := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjJ, hjne⟩
    by_contra hcon
    exact hjne (by rw [hval j hjJ, if_neg hcon])
  exact le_trans (Finset.card_le_card hsub) (hcard n hn)


/-- **Conjecture C9, lower half.**  Under Petersson-type quasi-orthogonality, an aligned AFE
of overlap `r` has second moment at least `(D − eN) · r` times the sum of the blockwise
coefficient masses: the factor `r` of `secondMoment_overlap_le` is genuine, not an artefact
of Cauchy–Schwarz. -/
theorem secondMoment_aligned_lower (S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (D e : ℝ)
    (h : QuasiOrthogonal S lam N D e) (J r : ℕ) (A : ℕ → ℕ → ℂ) (L : ι → ℂ)
    (act : ℕ → Finset ℕ) (c : ℕ → ℂ) (hL : AFE S lam N J (fun _ => 1) A L)
    (hal : AlignedOverlap N J A act c) (hcard : ∀ n ∈ Finset.range N, (act n).card = r) :
    (D - e * N) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2)
      ≤ ∑ f ∈ S, ‖L f‖ ^ 2 := by
  have hrw : ∑ f ∈ S, ‖L f‖ ^ 2
      = ∑ f ∈ S, ‖linForm lam N (fun n => ∑ j ∈ Finset.range J, (1 : ℂ) * A j n) f‖ ^ 2 :=
    Finset.sum_congr rfl fun f hf => by
      rw [afe_eq_linForm_aggregate S lam N J (fun _ => 1) A L hL hf]
  rw [hrw, ← sum_normSq_aggregate_aligned N J r A act c hal hcard]
  exact lowerBound_of_quasiOrthogonal S lam N D e h _



open AsaiSecondMoment in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (D e : ℝ) (h : QuasiOrthogonal S lam N D e) (hreg : 2 * (e * N) ≤ D) (J r : ℕ)
    (A : ℕ → ℕ → ℂ) (L : ι → ℂ) (act : ℕ → Finset ℕ) (c : ℕ → ℂ)
    (hL : AFE S lam N J (fun _ => 1) A L) (hal : AlignedOverlap N J A act c)
    (hcard : ∀ n ∈ Finset.range N, (act n).card = r) :
    (D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2)
        ≤ ∑ f ∈ S, ‖L f‖ ^ 2 ∧
      ∑ f ∈ S, ‖L f‖ ^ 2
        ≤ (3 * D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2) := by
  have hM0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun n _ => by positivity
  have hrM0 : (0 : ℝ) ≤ (r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 :=
    mul_nonneg (Nat.cast_nonneg r) hM0
  constructor
  · refine le_trans ?_
      (secondMoment_aligned_lower S lam N D e h J r A L act c hL hal hcard)
    have : D / 2 ≤ D - e * N := by linarith
    exact mul_le_mul_of_nonneg_right this hrM0
  · have hC0 : (0 : ℝ) ≤ D + e * N := quasiOrthogonal_const_nonneg S lam N D e hN h
    have hbound := secondMoment_overlap_le S lam N (D + e * N) hC0
      (largeSieve_of_quasiOrthogonal S lam N D e h) J r (fun _ => 1) A L hL
      (overlapMultiplicity_of_aligned N J r A act c hal fun n hn => le_of_eq (hcard n hn))
    have hsimp : ∑ j ∈ Finset.range J,
        ‖(1 : ℂ)‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
          = ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 := by
      simp
    rw [hsimp] at hbound
    refine hbound.trans ?_
    have hstep : (D + e * N) * (r : ℝ) ≤ (3 * D / 2) * (r : ℝ) := by
      have : D + e * N ≤ 3 * D / 2 := by linarith
      exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg r)
    calc (D + e * N) * (r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
        ≤ (3 * D / 2) * (r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hstep hM0
      _ = (3 * D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J,
            ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2) := by ring
