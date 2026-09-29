-- Prove2me | solution 1 for VRSubSqrt2.floor_gamma_le_exponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:14.781283+00:00
-- url     : https://prove2.me/submissions/35424913-dec5-4c1f-ae35-ffc1461fc182

-- Sol generated from Bridges/VietorisRipsSubSqrt2LowerBound.lean
import Mathlib
import Definitions.Def_Bridges_VietorisRipsSubSqrt2LowerBound
import Theorems.Thm_VRSubSqrt2_radius_le_iff

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


/-- On `[1, √2)`, the rate is positive. -/
theorem gamma_pos {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c < Real.sqrt 2) : 0 < gamma c := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hden : 0 < Real.sqrt 2 - 1 := by
    have h1 : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hnum : 0 < Real.sqrt 2 / c - 1 := by
    have : 1 < Real.sqrt 2 / c := by rw [lt_div_iff₀ hc0]; linarith
    linarith
  exact div_pos hnum hden

/-- On `[1, √2)`, the rate is at most `1`. -/
theorem gamma_le_one {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c < Real.sqrt 2) : gamma c ≤ 1 := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hden : 0 < Real.sqrt 2 - 1 := by
    have h1 : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  rw [gamma, div_le_one hden]
  have : Real.sqrt 2 / c ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ hc0]; nlinarith [Real.sqrt_nonneg 2]
  linarith





/-! ## The approximation lower bound -/


/-! ## Headline connector -/



open VRSubSqrt2 in
theorem solution{n : ℕ} (hn : 0 < n) {c : ℝ}
    (hc1 : 1 ≤ c) (hc2 : c < Real.sqrt 2) :
    ⌊(n : ℝ) * gamma c⌋₊ ≤ exponent c n := by
  set K := ⌊(n : ℝ) * gamma c⌋₊ with hK
  have hg0 : 0 ≤ gamma c := le_of_lt (gamma_pos hc1 hc2)
  have hng : (0:ℝ) ≤ (n:ℝ) * gamma c := by positivity
  have hKn : K ≤ n := by
    rw [hK]
    calc ⌊(n:ℝ) * gamma c⌋₊ ≤ ⌊(n:ℝ)⌋₊ := by
          apply Nat.floor_le_floor
          nlinarith [gamma_le_one hc1 hc2, Nat.cast_nonneg (α := ℝ) n]
      _ = n := Nat.floor_natCast n
  set A : Finset (Fin n) :=
    (Finset.range K).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) hKn) with hA
  have hAcard : A.card = K := by rw [hA, Finset.card_attachFin, Finset.card_range]
  have hsub : A ⊆ activeSet n (Real.sqrt 2 / c) := by
    intro i hi
    rw [hA, Finset.mem_attachFin, Finset.mem_range] at hi
    rw [activeSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [radius_le_iff hn]
    have hle : (i:ℕ) + 1 ≤ K := hi
    calc ((i:ℕ):ℝ) + 1 ≤ (K:ℝ) := by exact_mod_cast hle
      _ ≤ (n:ℝ) * gamma c := Nat.floor_le hng
  calc K = A.card := hAcard.symm
    _ ≤ (activeSet n (Real.sqrt 2 / c)).card := Finset.card_le_card hsub
