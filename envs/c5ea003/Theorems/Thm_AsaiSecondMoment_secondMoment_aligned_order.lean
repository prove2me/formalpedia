-- Prove2me | Theorems.Thm_AsaiSecondMoment_secondMoment_aligned_order
-- name    : AsaiSecondMoment.secondMoment_aligned_order
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:02:33.404964+00:00
-- url     : https://prove2.me/theorems/615b9d9f-c939-4c98-91fa-14163aa1f8f5
-- title:
--   Conjecture C9, settled: the exact order at intermediate overlap.
-- statement:
--   **Conjecture C9, settled: the exact order at intermediate overlap.**  In the
--   Kloosterman-controlled regime `2eN ≤ D`, an aligned AFE of overlap `r` has
--   `∑_f |L f|² ≍ D · r · ∑_j ‖A j‖²`, between `D/2` and `3D/2` times it.  For `r = 1` this is the
--   spectrally separated case, for `r = J` the flagship case, and for `1 < r < J` it shows that
--   the interpolation of `secondMoment_overlap_le` is of the correct order.
--
--   ```lean
--   theorem AsaiSecondMoment.secondMoment_aligned_order(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
--       (D e : ℝ) (h : QuasiOrthogonal S lam N D e) (hreg : 2 * (e * N) ≤ D) (J r : ℕ)
--       (A : ℕ → ℕ → ℂ) (L : ι → ℂ) (act : ℕ → Finset ℕ) (c : ℕ → ℂ)
--       (hL : AFE S lam N J (fun _ => 1) A L) (hal : AlignedOverlap N J A act c)
--       (hcard : ∀ n ∈ Finset.range N, (act n).card = r) :
--       (D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2)
--           ≤ ∑ f ∈ S, ‖L f‖ ^ 2 ∧
--         ∑ f ∈ S, ‖L f‖ ^ 2
--           ≤ (3 * D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiOverlapMultiplicity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiOverlapMultiplicity.lean#L320

-- Thm stub generated from Novelty/AsaiOverlapMultiplicity.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiOverlapMultiplicity
import Definitions.Def_Novelty_AsaiSecondMoment
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

theorem AsaiSecondMoment.secondMoment_aligned_order(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (D e : ℝ) (h : QuasiOrthogonal S lam N D e) (hreg : 2 * (e * N) ≤ D) (J r : ℕ)
    (A : ℕ → ℕ → ℂ) (L : ι → ℂ) (act : ℕ → Finset ℕ) (c : ℕ → ℂ)
    (hL : AFE S lam N J (fun _ => 1) A L) (hal : AlignedOverlap N J A act c)
    (hcard : ∀ n ∈ Finset.range N, (act n).card = r) :
    (D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2)
        ≤ ∑ f ∈ S, ‖L f‖ ^ 2 ∧
      ∑ f ∈ S, ‖L f‖ ^ 2
        ≤ (3 * D / 2) * ((r : ℝ) * ∑ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2) := by sorry
