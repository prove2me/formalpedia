-- Prove2me | solution 1 for VRSubSqrt2.radius_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:54.215267+00:00
-- url     : https://prove2.me/submissions/c2959710-b8bd-4dda-addc-fef374a36fd9

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





/-! ## `metricD` is a genuine (ultra)metric -/






/-! ## Clique ⇒ exponentially many simplices (the counting bridge) -/



/-! ## The graded active set is a clique -/




/-! ## The effective exponent `γ(c)` -/








/-! ## The approximation lower bound -/


/-! ## Headline connector -/



open VRSubSqrt2 in
theorem solution{n : ℕ} (hn : 0 < n) {c : ℝ} (i : ℕ) :
    radius n i ≤ Real.sqrt 2 / c ↔ ((i : ℝ) + 1) ≤ (n : ℝ) * gamma c := by
  have hden : (0:ℝ) < Real.sqrt 2 - 1 := by
    have h1 : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rw [radius, gamma]
  rw [show (n:ℝ) * ((Real.sqrt 2 / c - 1)/(Real.sqrt 2 - 1))
        = ((n:ℝ) * (Real.sqrt 2 / c - 1))/(Real.sqrt 2 - 1) by ring]
  rw [le_div_iff₀ hden]
  constructor
  · intro h
    have h' : (Real.sqrt 2 - 1) * ((i:ℝ)+1) / n ≤ Real.sqrt 2 / c - 1 := by linarith
    rw [div_le_iff₀ hnpos] at h'
    nlinarith
  · intro h
    have h' : (Real.sqrt 2 - 1) * ((i:ℝ)+1) / n ≤ Real.sqrt 2 / c - 1 := by
      rw [div_le_iff₀ hnpos]; nlinarith
    linarith
