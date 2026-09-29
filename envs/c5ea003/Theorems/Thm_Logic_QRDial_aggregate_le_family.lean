-- Prove2me | Theorems.Thm_Logic_QRDial_aggregate_le_family
-- name    : Logic.QRDial.aggregate_le_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:32:36.655885+00:00
-- url     : https://prove2.me/theorems/dc45f549-8a49-4114-b46b-0e7370c14501
-- title:
--   Collapsing a window into one count statistic can only lose information.
-- statement:
--   **Collapsing a window into one count statistic can only lose information.**  The
--   aggregate dial `S = Σ_j s_j` — the shape of a product-form count such as
--   `#{ℓ ≤ L : N is a QR mod ℓ}` — has squared correlation at most the capture budget of the
--   family it aggregates.  Hence a measured `S_prod` reading is a lower bound for its window,
--   and the family ceiling of cycle 2 is the correct quantity to test the `H1` bar against.
--
--   ```lean
--   theorem Logic.QRDial.aggregate_le_family(y : ι → ℝ) (s : κ → ι → ℝ) (hy : 0 < var y)
--       (hs : ∀ j, 0 < var (s j)) (horth : ∀ j l, j ≠ l → cov (s j) (s l) = 0) :
--       corrSq y (fun i => ∑ j, s j i) ≤ ∑ j, corrSq y (s j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QRDialWindowExtension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QRDialWindowExtension.lean#L117

-- Thm stub generated from Logic/QRDialWindowExtension.lean
import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialMultiCapture
/-
# Cycle 3: the capture *budget* of a prime window, and what the `ℓ ≤ 10⁶` extension must supply

Cycle 2 (`Logic.QRDialMultiCapture`) proved that for a pairwise-uncorrelated family of dials
the total linearly explained fraction of the target is exactly the sum of the individual
squared correlations, so the pre-registered `H1` bar is met only if
`Σ_j r_j² ≥ 0.30`.  This file turns that sum into a *budget* and derives the structural
constraints the named follow-up experiment (a product-form dial over all primes `ℓ ≤ 10⁶`,
~78k Legendre symbols) has to satisfy.

Main results.

* `capture_budget_le_one` — **Bessel inequality for dials.**  For any orthogonal family the
  capture budget `Σ_j r_j²` is at most `1`.  The explained shares of orthogonal dials add,
  and they can never overdraw the variance of the target.  Consequence: a family of `m`
  orthogonal dials of *equal* strength has `r² ≤ 1/m` per dial
  (`uniform_correlation_ceiling`), so "many weak symbols" is a genuine constraint, not a
  free lunch.
* `var_sum_of_orthogonal`, `aggregate_le_family` — **collapsing a window into one count
  statistic can only lose.**  The single aggregated dial `S = Σ_j s_j` (which is exactly
  what a product-form count `#{ℓ : N is a QR mod ℓ}` is: a sum of per-prime indicators)
  satisfies `r²(y, S) ≤ Σ_j r²(y, s_j)`.  So the recorded `S_prod` reading is a *lower*
  bound for the window it summarises, and the family bound of cycle 2 is the right ceiling
  to test against.
* `window_transfer_requirement` — **the pre-registered decision rule for the follow-up.**
  With the tested window `ℓ ≤ 400` capped at `0.1422` of squared correlation, meeting the
  `0.30` bar forces the extension window `400 < ℓ ≤ 10⁶` to supply at least `0.1578` on its
  own.
* `carrier_dimension_lower_bound`, `exp576_carrier_dimension` — **how many mechanisms the
  carrier needs.**  If no single orthogonal dial exceeds `c`, reaching the bar takes at least
  `0.3/c` of them; at the recorded ceiling `c = 0.0781` that is at least four mutually
  uncorrelated mechanisms.
* `extension_per_symbol_requirement`, `exp576_window_extension_target` — **a per-symbol
  target.**  Spreading `0.1578` over at most `78 498` primes forces at least one individual
  Legendre-symbol dial to carry `r² ≥ 2·10⁻⁶`.  That is a falsifiable, per-symbol
  prediction: if every symbol in the extension window measures below `2·10⁻⁶`, the
  scale-shift hypothesis is refuted and the residual `u ≈ 10` clustering is carried by
  structure outside the QR dial family altogether.

Everything is exact finite-sample algebra; the measured numbers enter only as hypotheses.
-/

open Finset

open Logic.QRDial

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ## Nonnegativity plumbing -/




/-! ## A Bessel inequality for orthogonal dials -/



/-! ## Aggregating a window into a single count statistic -/

theorem Logic.QRDial.aggregate_le_family(y : ι → ℝ) (s : κ → ι → ℝ) (hy : 0 < var y)
    (hs : ∀ j, 0 < var (s j)) (horth : ∀ j l, j ≠ l → cov (s j) (s l) = 0) :
    corrSq y (fun i => ∑ j, s j i) ≤ ∑ j, corrSq y (s j) := by sorry
