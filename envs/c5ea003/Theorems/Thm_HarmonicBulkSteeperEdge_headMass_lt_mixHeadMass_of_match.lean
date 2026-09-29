-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_headMass_lt_mixHeadMass_of_match
-- name    : HarmonicBulkSteeperEdge.headMass_lt_mixHeadMass_of_match
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:31.002985+00:00
-- url     : https://prove2.me/theorems/95cb6ab2-3282-4420-a906-47bce79b47ff
-- title:
--   Strict single-crossing window law.
-- statement:
--   **Strict single-crossing window law.**  If a pure power law with exponent `c` matches
--   the head mass of a genuine bulk × edge mixture on the window `{1, …, m₂}`, then on every
--   narrower window it reports *strictly* less head mass than the mixture.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.headMass_lt_mixHeadMass_of_match{w a b c : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
--       (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
--       (hmatch : headMass c n m₂ = mixHeadMass w a b n m₂) :
--       headMass c n m₁ < mixHeadMass w a b n m₁ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HarmonicBulkSteeperEdgeStrict.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HarmonicBulkSteeperEdgeStrict.lean#L158

-- Thm stub generated from Probability/HarmonicBulkSteeperEdgeStrict.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
/-
  # Strict single-crossing for the harmonic-bulk × steeper-edge kernel

  `Probability.HarmonicBulkSteeperEdge` proves that the window-implied exponent of a
  two-component (bulk × edge) power-law kernel is **antitone** in the window width:
  a narrower head window never reports a shallower exponent than a wider one
  (`implied_exponent_antitone`).  The inequality obtained there is non-strict, because the
  quasiconvexity input (`two_term_rpow_quasiconvex`) was proved through a non-strict
  weighted AM–GM.  This file closes that gap: for a genuine mixture (`0 < w < 1`,
  `a < b`) the window law is **strict**.

  ## Contents

  * `rpow_log_convex` / `rpow_log_strictConvex` — a single real power `x ↦ x ^ e` is convex
    in `log x`, strictly so when `e ≠ 0` (via strict convexity of `exp`).
  * `mixRatio_strict_log_convex` — the mixture-to-power-law ratio is *strictly* convex in
    the logarithmic variable: since `a < b`, at least one of the two exponents `c - a`,
    `c - b` is nonzero, so a strictly convex summand is always present.
  * `mixRatio_lt_of_crossed_strict` — **strict no-return.**  If the ratio is at or below a
    level at `k₁` and at or above it at some `k₀ > k₁`, then it is *strictly above* the
    level at every `k > k₀`.  The base file's no-return lemma needs a strict crossing;
    strict convexity upgrades a weak crossing to a strict one-sided conclusion.
  * `headMass_lt_mixHeadMass_of_match` — a pure power law matching the mixture on a window
    reports **strictly** less head mass on every narrower window.
  * `implied_exponent_strictAnti` — hence `c₂ < c₁`: narrower windows report *strictly*
    steeper implied exponents.  This closes direction 1 of the previous cycle's
    `FUTURE_DIRECTIONS.md`.
  * `no_mixture_matches_two_windows_with_equal_exponent` — the diagnostic consequence: two
    head windows reporting the *same* implied exponent certify that the kernel is not a
    bulk × edge mixture.
  * `harmonic_edge_mixture_window_exponents_strictAnti` — the capstone for the recorded
    harmonic-bulk / quadratic-edge kernel.

  The proof of the strict window law is structurally simpler than the non-strict one.  The
  strict no-return lemma shows that on the wide window `{1,…,m₂}` the discrepancy
  `d k = mix k - θ · pw c k` has a genuine single sign change: it is positive on an initial
  segment and strictly negative afterwards.  Each of the two possible positions of the
  narrow window relative to that sign change then yields a strict inequality.
-/

open Finset

open HarmonicBulkSteeperEdge

/-! ## Strict log-convexity of real powers -/



/-! ## Strict convexity of the mixture-to-power-law ratio -/



/-! ## The strict single-crossing window law -/

theorem HarmonicBulkSteeperEdge.headMass_lt_mixHeadMass_of_match{w a b c : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (hab : a < b) {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (hmatch : headMass c n m₂ = mixHeadMass w a b n m₂) :
    headMass c n m₁ < mixHeadMass w a b n m₁ := by sorry
