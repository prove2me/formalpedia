-- Prove2me | solution 1 for AdjSum.fekete_growth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:39:10.954752+00:00
-- url     : https://prove2.me/submissions/c99b3527-1c09-464b-9731-318a43d96a61

-- Sol generated from Applications/AdjacentSumPolytopes/DominantGrowth.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_DominantGrowth
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Theorems.Thm_AdjSum_tendsto_mul_div_add_one

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



/-! ## The diagonal loop counts -/








/-! ## Existence of the dominant growth rate -/




open AdjSum in
theorem solution(g : ℕ → ℕ) (hpos : ∀ n, 1 ≤ g n) (hsuper : ∀ m n, g m * g n ≤ g (m + n))
    (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hlb : ∀ n, A ^ n ≤ g (n + 1)) (hub : ∀ n, g n ≤ B ^ n) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => Real.log (g n) / n) atTop (𝓝 L) ∧
      Real.log A ≤ L ∧ L ≤ Real.log B := by
  have hgpos : ∀ n, (0:ℝ) < (g n : ℝ) := fun n => by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (hpos n)
  set u : ℕ → ℝ := fun n => -Real.log (g n) with hu
  have hsub : Subadditive u := by
    intro m n
    have h1 : Real.log (g m) + Real.log (g n) ≤ Real.log (g (m + n)) := by
      rw [← Real.log_mul (ne_of_gt (hgpos m)) (ne_of_gt (hgpos n))]
      apply Real.log_le_log (mul_pos (hgpos m) (hgpos n))
      exact_mod_cast hsuper m n
    simp only [hu]
    linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hle : ∀ n : ℕ, Real.log (g n) / n ≤ Real.log B := by
    intro n
    match n with
    | 0 => simpa using hlogB
    | (k + 1) =>
      have hn : (0:ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have h1 : Real.log (g (k + 1)) ≤ ((k + 1 : ℕ) : ℝ) * Real.log B := by
        calc Real.log (g (k + 1)) ≤ Real.log ((B:ℝ) ^ (k + 1)) := by
              apply Real.log_le_log (hgpos _)
              exact_mod_cast hub (k + 1)
          _ = ((k + 1 : ℕ) : ℝ) * Real.log B := by rw [Real.log_pow]
      rw [div_le_iff₀ hn]
      linarith
  have hbdd : BddBelow (Set.range fun n => u n / n) := by
    refine ⟨-Real.log B, ?_⟩
    rintro x ⟨n, rfl⟩
    have h := hle n
    simp only [hu, neg_div]
    linarith
  have htend : Filter.Tendsto (fun n : ℕ => Real.log (g n) / n) atTop (𝓝 (-hsub.lim)) := by
    have h := hsub.tendsto_lim hbdd
    have h2 : (fun n : ℕ => Real.log (g n) / n) = fun n : ℕ => -(u n / n) := by
      funext n; simp only [hu]; ring
    rw [h2]; exact h.neg
  refine ⟨-hsub.lim, htend, ?_, le_of_tendsto htend (Filter.Eventually.of_forall hle)⟩
  -- lower bound via the shifted subsequence
  have hshift : Filter.Tendsto (fun n : ℕ => Real.log (g (n + 1)) / ((n : ℝ) + 1)) atTop
      (𝓝 (-hsub.lim)) := by
    have h := htend.comp (Filter.tendsto_add_atTop_nat 1)
    refine h.congr (fun n => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring
  have hcomp : ∀ n : ℕ, (n : ℝ) * Real.log A / ((n : ℝ) + 1)
      ≤ Real.log (g (n + 1)) / ((n : ℝ) + 1) := by
    intro n
    have hn : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : (n : ℝ) * Real.log A ≤ Real.log (g (n + 1)) := by
      calc (n : ℝ) * Real.log A = Real.log ((A : ℝ) ^ n) := by rw [Real.log_pow]
        _ ≤ Real.log (g (n + 1)) := by
            apply Real.log_le_log (by positivity)
            · exact_mod_cast hlb n
    gcongr
  exact le_of_tendsto_of_tendsto' (tendsto_mul_div_add_one (Real.log A)) hshift hcomp
