-- Prove2me | solution 1 for VRSubSqrt2.dist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:45:48.463935+00:00
-- url     : https://prove2.me/submissions/fdbbf105-cb08-462e-b6f6-8900e47faef9

-- Sol generated from Bridges/VietorisRipsSubSqrt2LowerBound.lean
import Mathlib
import Definitions.Def_Bridges_VietorisRipsSubSqrt2LowerBound

/-!
# A cross-domain bridge: sub-√2 Vietoris–Rips approximations force exponentially many
  simplices, with an effective exponent `γ(c)` vanishing at the √2 threshold

This file connects three *a priori* separate areas around a single explicit construction:

* **Metric geometry.**  We build, for every `n`, a genuine finite metric space on
  `Fin n` — in fact an *ultrametric* — whose non-zero distances are graded through the
  window `[1, √2]` (`dist_isMetric`: symmetry, non-negativity, vanishing on the diagonal,
  and the (strong) triangle inequality).

* **Topological data analysis / interleavings.**  The Vietoris–Rips complex `VRcomplex`
  is the flag complex of the proximity relation; a `c`-approximation `IsCApprox` is a
  one-sided multiplicative interleaving of simplicial filtrations, the standard notion of a
  finitely-presented `c`-approximation used by approximation algorithms in TDA.

* **Extremal / enumerative combinatorics.**  A metric *clique* of size `m` at scale `r`
  forces `2 ^ m` simplices into `VRcomplex` (`two_pow_card_le_card_VRcomplex`): the whole
  power set of the clique is present.  This is the counting engine converting geometry into
  exponential complexity.

## The theorem (the connector)

For every `c ∈ [1, √2)` and every `n`, **any** `c`-approximation `G` of the Vietoris–Rips
filtration of `metricD n` stores at least `2 ^ ⌊γ(c) · n⌋` simplices at scale `√2`, where

  `γ(c) = (√2 / c − 1) / (√2 − 1)`

is effectively computable, satisfies `0 < γ(c) ≤ 1` on `[1, √2)`, and
`lim_{c → √2⁻} γ(c) = 0` (`gamma_tendsto_nhdsWithin`).  Thus the guaranteed exponential
rate degrades continuously to `0` exactly as the approximation factor approaches the
sharp √2 threshold, and no non-trivial rate survives at `c = √2`.

## Main results

* `dist_isMetric` — `metricD n` is a genuine (ultra)metric on `Fin n`.
* `two_pow_card_le_card_VRcomplex` — clique ⇒ exponentially many simplices (the bridge).
* `two_pow_activeCard_le_VRcomplex` — the graded active set is such a clique.
* `gamma_pos`, `gamma_le_one`, `gamma_tendsto_nhdsWithin` — the effective exponent and its
  behaviour at the √2 threshold.
* `floor_gamma_le_exponent` — the active set realises the rate `⌊γ(c) · n⌋`.
* `approx_card_lower_bound` — any `c`-approximation has `2 ^ (exponent c n)` simplices at
  scale `√2`.
* `subSqrt2_exponential_lower_bound` — **headline connector**: the explicit
  `2 ^ ⌊γ(c) · n⌋` lower bound together with `0 < γ(c) ≤ 1` and the vanishing limit.
-/

noncomputable section

open Finset Classical

open VRSubSqrt2

/-! ## The graded ultrametric -/






/-! ## Basic radius facts -/

theorem radius_nonneg_gap : (0 : ℝ) ≤ Real.sqrt 2 - 1 := by
  have : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- Radii are at least `1`. -/
theorem one_le_radius {n i : ℕ} (hn : 0 < n) : 1 ≤ radius n i := by
  have hg := radius_nonneg_gap
  have : (0:ℝ) ≤ (Real.sqrt 2 - 1) * ((i : ℝ) + 1) / (n : ℝ) := by positivity
  simp only [radius]; linarith

/-- Radii of genuine vertices are at most `√2`. -/
theorem radius_le_sqrt2 {n : ℕ} (i : Fin n) : radius n (i : ℕ) ≤ Real.sqrt 2 := by
  have hg := radius_nonneg_gap
  have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast i.pos
  have hi : ((i:ℕ):ℝ) + 1 ≤ (n:ℝ) := by
    have : (i:ℕ) + 1 ≤ n := i.2
    exact_mod_cast this
  have : (Real.sqrt 2 - 1) * ((i : ℝ) + 1) / (n : ℝ) ≤ (Real.sqrt 2 - 1) := by
    rw [div_le_iff₀ hn]; exact mul_le_mul_of_nonneg_left hi hg
  simp only [radius]; linarith


/-! ## `metricD` is a genuine (ultra)metric -/

theorem metricD_dist_self (n : ℕ) (i : Fin n) : metricD n i i = 0 := by
  simp [metricD]


theorem metricD_dist_nonneg {n : ℕ} (hn : 0 < n) (i j : Fin n) : 0 ≤ metricD n i j := by
  simp only [metricD]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h]; linarith [one_le_radius (n:=n) (i := max (i:ℕ) (j:ℕ)) hn]



/-! ## Clique ⇒ exponentially many simplices (the counting bridge) -/



/-! ## The graded active set is a clique -/




/-! ## The effective exponent `γ(c)` -/








/-! ## The approximation lower bound -/


/-! ## Headline connector -/



open VRSubSqrt2 in
theorem solution{n : ℕ} (hn : 0 < n) (i j k : Fin n) :
    metricD n i k ≤ metricD n i j + metricD n j k := by
  have h2sqrt : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  by_cases hik : i = k
  · subst hik
    simp only [metricD_dist_self]
    linarith [metricD_dist_nonneg hn i j, metricD_dist_nonneg hn j i]
  · have hL : metricD n i k ≤ Real.sqrt 2 := by
      simp only [metricD, if_neg hik]
      rcases le_total (i:ℕ) (k:ℕ) with hle|hle
      · rw [max_eq_right hle]; exact radius_le_sqrt2 k
      · rw [max_eq_left hle]; exact radius_le_sqrt2 i
    by_cases hij : i = j
    · subst hij; simp only [metricD_dist_self, zero_add, le_refl]
    · by_cases hjk : j = k
      · subst hjk; simp only [metricD_dist_self, add_zero, le_refl]
      · have h1 : (1:ℝ) ≤ metricD n i j := by
          simp only [metricD, if_neg hij]; exact one_le_radius hn
        have h2 : (1:ℝ) ≤ metricD n j k := by
          simp only [metricD, if_neg hjk]; exact one_le_radius hn
        linarith
