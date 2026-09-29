-- Prove2me | Theorems.Thm_AdjSum_fekete_growth
-- name    : AdjSum.fekete_growth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:14:54.662946+00:00
-- url     : https://prove2.me/theorems/db7013c6-9875-4ce9-ae46-c8c87e6ce75d
-- title:
--   Fekete growth lemma.
-- statement:
--   **Fekete growth lemma.**  A supermultiplicative sequence of positive integers
--   squeezed between the exponentials `Aⁿ` and `Bⁿ` has a well-defined exponential growth
--   rate, lying between `log A` and `log B`.
--
--   ```lean
--   theorem AdjSum.fekete_growth(g : ℕ → ℕ) (hpos : ∀ n, 1 ≤ g n) (hsuper : ∀ m n, g m * g n ≤ g (m + n))
--       (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hlb : ∀ n, A ^ n ≤ g (n + 1)) (hub : ∀ n, g n ≤ B ^ n) :
--       ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => Real.log (g n) / n) atTop (𝓝 L) ∧
--         Real.log A ≤ L ∧ L ≤ Real.log B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/DominantGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/DominantGrowth.lean#L56

-- Thm stub generated from Applications/AdjacentSumPolytopes/DominantGrowth.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_DominantGrowth
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth

/-!
# The dominant growth rate of the adjacent-sum model

The bounds of `Applications.AdjacentSumPolytopes.Growth` bracket the counts between two
exponentials but do not say that a growth *rate* exists.  Here we prove that it does,
by a Fekete (subadditivity) argument applied to the diagonal counts

`diagCount s n = (adjMat s ^ n) 0 0 = #{open points of length n+1 with x₀ = xₙ = 0}`,

which are supermultiplicative because concatenation of two loops at the state `0` is a
loop at `0`.  The resulting limit

`λ_s = exp (lim_{n} (log diagCount s n)/n)`

is the reciprocal of the dominant real pole of the shared characteristic denominator,
and we show `⌊s/2⌋ + 1 ≤ λ_s ≤ s + 1` (in logarithmic form).

-- !-- Lab Notes -- !--
* **Hypothesis.** Loops at the state `0` are supermultiplicative, so Fekete's lemma
  applies and the exponential growth rate exists; the block bounds of the previous file
  bracket it.
* **Experiment.** `diagCount 2 n = 1, 1, 3, 6, 14, 31, 70, 157, ...` and the ratios
  `1, 3, 2, 2.33, 2.21, 2.26, 2.24, ...` oscillate towards the dominant root `≈ 2.2470`
  of `x³ − 2x² − x + 1`, comfortably inside `[2, 3]`.  For `s = 3`:
  `1, 1, 4, 10, 30, 85, 246, 707` with ratios approaching `≈ 2.87 ∈ [2, 4]`.
* **Analysis.** The `Subadditive` machinery of Mathlib needs `BddBelow` of `u n / n`
  where `u n = − log (diagCount s n)`; the upper block bound supplies exactly that.
  The lower bound on the limit needs a shifted subsequence, since `diagCount s 0 = 1`
  carries no information.
* **Critique.** The statement is not vacuous: `diagCount s n ≥ 1` is proved (the all-zero
  point is always admissible), so all logarithms are of positive numbers, and for
  `s ≥ 2` the limit is at least `log 2 > 0`, i.e. genuinely exponential growth.
-/

open AdjSum

open Finset Matrix Filter Topology

/-! ## A Fekete-type growth lemma -/

theorem AdjSum.fekete_growth(g : ℕ → ℕ) (hpos : ∀ n, 1 ≤ g n) (hsuper : ∀ m n, g m * g n ≤ g (m + n))
    (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hlb : ∀ n, A ^ n ≤ g (n + 1)) (hub : ∀ n, g n ≤ B ^ n) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => Real.log (g n) / n) atTop (𝓝 L) ∧
      Real.log A ≤ L ∧ L ≤ Real.log B := by sorry
