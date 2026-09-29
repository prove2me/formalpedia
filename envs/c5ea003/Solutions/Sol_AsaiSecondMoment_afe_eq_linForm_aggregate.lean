-- Prove2me | solution 1 for AsaiSecondMoment.afe_eq_linForm_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:23:35.899579+00:00
-- url     : https://prove2.me/submissions/9020cb88-3a72-489a-944d-b1695ba5de2e

-- Sol generated from Novelty/AsaiSecondMomentLower.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiSecondMoment
/-
# Disjoint blocks: a matching lower bound and the removal of the `J²` loss

This file settles conjecture **C3** of `FUTURE_DIRECTIONS.md` for the Asai second-moment
framework of `Novelty.AsaiLargeSieve` / `Novelty.AsaiSecondMoment`.

The flagship theorem `AsaiSecondMoment.asai_second_moment_k_aspect` bounds the second moment
of a family of central values admitting a `J`-block approximate functional equation by
`J² · C · B`, the two factors of `J` coming from a Cauchy–Schwarz inequality applied to the
sum over the blocks.  C3 predicted that if the blocks are **spectrally separated** — their
coefficient vectors have pairwise disjoint supports, which is exactly the situation of a
dyadic decomposition of the Dirichlet series into ranges `n ≍ 2^j` — then

* the `J²` degrades to a single `J`, and
* a *matching lower bound* of the same shape holds.

Both are proved here, and the mechanism is the same in the two directions: for disjointly
supported blocks the whole approximate functional equation collapses to **one** Dirichlet
polynomial (`AsaiSecondMoment.afe_eq_linForm_aggregate`, which needs no disjointness at all),
and disjointness then converts the `ℓ²`-mass of the aggregated coefficient vector into the sum
of the blockwise masses (`sum_normSq_aggregate_of_disjoint`).

Main results:

* `AsaiSecondMoment.afe_eq_linForm_aggregate` — an AFE is a single Dirichlet polynomial with
  coefficients `c n = ∑_{j<J} w j · A j n`.
* `AsaiSecondMoment.sum_normSq_aggregate_of_disjoint` — for blocks separated by a block-index
  function `b`, `∑_{n<N} |c n|² = ∑_{j<J} |w j|² ∑_{n<N} |A j n|²`.
* `AsaiSecondMoment.secondMoment_disjoint_le` — the upper bound `C · ∑_j |w j|²‖A j‖²`, hence
  `secondMoment_disjoint_uniform`: `∑_f |L f|² ≤ J · C · B`, one factor of `J` better than the
  flagship bound.
* `AsaiSecondMoment.secondMoment_disjoint_lower` — the matching lower bound
  `(D − eN) · ∑_j |w j|²‖A j‖² ≤ ∑_f |L f|²`.
* `AsaiSecondMoment.secondMoment_disjoint_order` — combining the two: in the
  Kloosterman-controlled regime `2eN ≤ D` the second moment of a spectrally separated AFE has
  the exact order `D · ∑_j |w j|²‖A j‖²`, up to the factor `3`.
* `AsaiSecondMoment.dyadic_support_disjoint` and `AsaiSecondMoment.secondMoment_dyadic` — the
  case that actually occurs in the paper: for a dyadic AFE (the `j`-th block supported in
  `[2^j, 2^{j+1})`, block index `Nat.log 2`) the bound is `C · W · B`, where `W` bounds the
  total archimedean weight mass `∑_j |w j|²`.  There is then no `J`-dependence at all.

Lab notes (Experimenter).  Sanity check of the gain: with `J = 2`, `w = (1,1)`,
`A 0 = (1,0)`, `A 1 = (0,1)` on `N = 2` and an orthonormal system with `D = 1`, `e = 0`, the
flagship bound gives `J²·C·B = 4·1·1 = 4`, the disjoint bound gives `J·C·B = 2`, and the true
value is `∑_f |L f|² = 2`, which is also what `secondMoment_disjoint_le` predicts exactly
(`C · ∑_j |w j|²‖A j‖² = 1 · 2 = 2`).  So the improvement is not merely formal: the disjoint
bound is attained while the flagship bound is off by the full factor `J`.  This computation is
not left informal — it is the theorem `secondMoment_disjoint_attained` below.

Critique (Critic).  The disjointness hypothesis is recorded by an explicit block-index
function `b : ℕ → ℕ` with `A j n = 0` unless `b n = j`; this is strictly weaker than requiring
the supports to be intervals, and it allows blocks to be empty.  No positivity of `D` or `e`
is assumed anywhere: the lower bound is vacuous (but true) when `D ≤ eN`, which is the honest
statement.  The upper bound `secondMoment_disjoint_le` does not use quasi-orthogonality at
all — any admissible large sieve constant works.
-/

open Finset Complex AsaiLargeSieve

open AsaiSecondMoment

variable {ι : Type*}








/-! ## The dyadic case -/




open AsaiSecondMoment in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N J : ℕ) (w : ℕ → ℂ)
    (A : ℕ → ℕ → ℂ) (L : ι → ℂ) (hL : AFE S lam N J w A L) {f : ι} (hf : f ∈ S) :
    L f = linForm lam N (fun n => ∑ j ∈ Finset.range J, w j * A j n) f := by
  rw [hL f hf]
  simp only [linForm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => by ring
