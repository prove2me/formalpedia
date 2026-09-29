-- Prove2me | solution 1 for AsaiSecondMoment.secondMoment_disjoint_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:33:47.853814+00:00
-- url     : https://prove2.me/submissions/5659a952-c635-4cde-b3b7-97fbdc9e9386

-- Sol generated from Novelty/AsaiSecondMomentLower.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiSecondMoment
import Theorems.Thm_AsaiSecondMoment_afe_eq_linForm_aggregate
import Theorems.Thm_AsaiSecondMoment_sum_normSq_aggregate_of_disjoint
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



/-- **C3, upper half.**  For a spectrally separated AFE the second moment is bounded by the
large sieve constant times the *sum* of the blockwise coefficient masses — there is no
Cauchy–Schwarz loss over the blocks. -/
theorem secondMoment_disjoint_le (S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hLS : LargeSieve S lam N C) (J : ℕ) (w : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (L : ι → ℂ) (b : ℕ → ℕ)
    (hL : AFE S lam N J w A L)
    (hsupp : ∀ j ∈ Finset.range J, ∀ n ∈ Finset.range N, b n ≠ j → A j n = 0) :
    ∑ f ∈ S, ‖L f‖ ^ 2
      ≤ C * ∑ j ∈ Finset.range J, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 := by
  have hrw : ∑ f ∈ S, ‖L f‖ ^ 2
      = ∑ f ∈ S, ‖linForm lam N (fun n => ∑ j ∈ Finset.range J, w j * A j n) f‖ ^ 2 :=
    Finset.sum_congr rfl fun f hf => by
      rw [afe_eq_linForm_aggregate S lam N J w A L hL hf]
  rw [hrw]
  refine (hLS _).trans_eq ?_
  rw [sum_normSq_aggregate_of_disjoint N J w A b hsupp]





/-! ## The dyadic case -/




open AsaiSecondMoment in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hLS : LargeSieve S lam N C) (J : ℕ) (w : ℕ → ℂ) (A : ℕ → ℕ → ℂ) (L : ι → ℂ)
    (b : ℕ → ℕ) (B : ℝ) (hL : AFE S lam N J w A L)
    (hsupp : ∀ j ∈ Finset.range J, ∀ n ∈ Finset.range N, b n ≠ j → A j n = 0)
    (hw : ∀ j ∈ Finset.range J, ‖w j‖ ≤ 1)
    (hB : ∀ j ∈ Finset.range J, ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 ≤ B) :
    ∑ f ∈ S, ‖L f‖ ^ 2 ≤ (J : ℝ) * C * B := by
  refine (secondMoment_disjoint_le S lam N C hLS J w A L b hL hsupp).trans ?_
  have hterm : ∀ j ∈ Finset.range J,
      ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 ≤ B := by
    intro j hj
    have hA0 : (0 : ℝ) ≤ ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => by positivity
    have h1 : ‖w j‖ ^ 2 ≤ 1 := by
      have := hw j hj
      nlinarith [norm_nonneg (w j)]
    calc ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
        ≤ 1 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hA0
      _ = ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2 := one_mul _
      _ ≤ B := hB j hj
  have hsum : ∑ j ∈ Finset.range J, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
      ≤ (J : ℝ) * B := by
    calc ∑ j ∈ Finset.range J, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
        ≤ ∑ _j ∈ Finset.range J, B := Finset.sum_le_sum hterm
      _ = (J : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc C * ∑ j ∈ Finset.range J, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range N, ‖A j n‖ ^ 2
      ≤ C * ((J : ℝ) * B) := mul_le_mul_of_nonneg_left hsum hC
    _ = (J : ℝ) * C * B := by ring
