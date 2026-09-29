-- Prove2me | Theorems.Thm_AsaiSecondMoment_secondMoment_disjoint_attained
-- name    : AsaiSecondMoment.secondMoment_disjoint_attained
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:03:06.759625+00:00
-- url     : https://prove2.me/theorems/782de69d-ce84-4dc4-8d7a-5162c4c6f8bc
-- title:
--   The disjoint-block bound is attained, and the flagship bound is not.
-- statement:
--   **The disjoint-block bound is attained, and the flagship bound is not.**  A concrete
--   orthonormal system with `N = J = 2`, unit weights and the two coordinate blocks: the second
--   moment equals `2`, the disjoint bound `C · ∑_j |w j|²‖A j‖²` equals `2` as well (equality),
--   while the flagship bound `J² · C · B` equals `4`.  So the factor `J` removed by
--   `secondMoment_disjoint_uniform` is exactly the truth, not an artefact of the proof.
--
--   ```lean
--   theorem AsaiSecondMoment.secondMoment_disjoint_attained:
--       let lam : Fin 2 → ℕ → ℂ := fun f n => if n = (f : ℕ) then 1 else 0
--       let w : ℕ → ℂ := fun _ => 1
--       let A : ℕ → ℕ → ℂ := fun j n => if n = j then 1 else 0
--       let L : Fin 2 → ℂ := fun _ => 1
--       AFE (Finset.univ : Finset (Fin 2)) lam 2 2 w A L
--         ∧ LargeSieve (Finset.univ : Finset (Fin 2)) lam 2 1
--         ∧ (∀ j ∈ Finset.range 2, ∀ n ∈ Finset.range 2, n ≠ j → A j n = 0)
--         ∧ (∑ f : Fin 2, ‖L f‖ ^ 2) = 2
--         ∧ (1 : ℝ) * ∑ j ∈ Finset.range 2, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range 2, ‖A j n‖ ^ 2 = 2
--         ∧ ((2 : ℝ)) ^ 2 * 1 * 1 = 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AsaiSecondMomentLower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AsaiSecondMomentLower.lean#L201

-- Thm stub generated from Novelty/AsaiSecondMomentLower.lean
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

theorem AsaiSecondMoment.secondMoment_disjoint_attained:
    let lam : Fin 2 → ℕ → ℂ := fun f n => if n = (f : ℕ) then 1 else 0
    let w : ℕ → ℂ := fun _ => 1
    let A : ℕ → ℕ → ℂ := fun j n => if n = j then 1 else 0
    let L : Fin 2 → ℂ := fun _ => 1
    AFE (Finset.univ : Finset (Fin 2)) lam 2 2 w A L
      ∧ LargeSieve (Finset.univ : Finset (Fin 2)) lam 2 1
      ∧ (∀ j ∈ Finset.range 2, ∀ n ∈ Finset.range 2, n ≠ j → A j n = 0)
      ∧ (∑ f : Fin 2, ‖L f‖ ^ 2) = 2
      ∧ (1 : ℝ) * ∑ j ∈ Finset.range 2, ‖w j‖ ^ 2 * ∑ n ∈ Finset.range 2, ‖A j n‖ ^ 2 = 2
      ∧ ((2 : ℝ)) ^ 2 * 1 * 1 = 4 := by sorry
