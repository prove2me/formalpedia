-- Prove2me | solution 1 for ChebotarevGeodesic.not_hasErrorExponent_of_intValued
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:59:17.399123+00:00
-- url     : https://prove2.me/submissions/1295d8f9-c196-49cd-81e7-b60abbe1c2a8

-- Sol generated from Shared/ChebotarevGeodesicIntegrality.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTorus
/-
# Integrality forces a non-negative optimal exponent

Continuation of `Shared.ChebotarevGeodesic`, `Shared.ChebotarevGeodesicOptimal` and
`Shared.ChebotarevGeodesicTorus`.

A geodesic counting function is *integer valued*, whereas the main terms occurring in the
prime geodesic and Chebotarev geodesic theorems (`li x`, `c·x^β`, `log x / (2 log ε)`, …) are
*continuous* and *unbounded*.  This file shows that this clash alone already forbids any
negative error exponent:

* `not_hasErrorExponent_of_intValued` : if `π` takes only integer values and `M` is continuous
  on `[1, ∞)` and tends to `+∞`, then `HasErrorExponent π M θ` fails for every `θ < 0`.
  The proof is an intermediate-value argument: choose `u` beyond which the error is `< 1/4`,
  use continuity of `M` to find `v ≥ u` with `M v = M u + 1/2`, and observe that
  `(π v - π u) - 1/2` is at distance `≥ 1/2` from `0` because `π v - π u ∈ ℤ`, while the two
  error bounds force it to be `< 1/2`.
* `optimalExponent_eq_zero_of_intValued` : consequently, an integer valued counting function
  with a bounded error has optimal exponent exactly `0`.
* `optimalExponent_torusFamily` : **conjecture C2 of `FUTURE_DIRECTIONS.md`.**  Every finite
  superposition of single-torus Chebotarev counting functions has optimal error exponent
  exactly `0`.  Hence the positive exponent `25/36` of the paper cannot be produced by any
  *finite* family of tori: it is a genuinely infinite (class-number) phenomenon.
* `le_optimalExponent_of_intValued` : for any integer valued counting function with continuous
  unbounded main term, `0 ≤ optimalExponent π M`; in particular no future improvement of the
  prime geodesic exponent can go below `0`.
-/


open Filter Set
open scoped Topology

open ChebotarevGeodesic

/-! ## The integrality obstruction -/




/-! ## Application: finite families of non-split tori -/






open ChebotarevGeodesic in
theorem solution{pi M : ℝ → ℝ} {θ : ℝ} (hθ : θ < 0)
    (hint : ∀ x, ∃ k : ℤ, pi x = (k : ℝ))
    (hcont : ContinuousOn M (Set.Ici (1 : ℝ)))
    (hlim : Tendsto M atTop atTop) :
    ¬ HasErrorExponent pi M θ := by
  intro h
  obtain ⟨C, hC, X, hX, hb⟩ := h (-θ / 2) (by linarith)
  have hexp : θ + -θ / 2 = θ / 2 := by ring
  have htend : Tendsto (fun x : ℝ => C * x ^ (θ / 2)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (θ / 2)) atTop (𝓝 0) := by
      have he : θ / 2 = -(-(θ / 2)) := by ring
      rw [he]
      exact tendsto_rpow_neg_atTop (by linarith)
    simpa using h0.const_mul C
  have hev : ∀ᶠ x : ℝ in atTop, C * x ^ (θ / 2) < 1 / 4 :=
    htend.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨U, hU⟩ := eventually_atTop.mp
    (hev.and ((eventually_ge_atTop X).and (eventually_ge_atTop (1 : ℝ))))
  set u : ℝ := max U 1 with hudef
  have huU : U ≤ u := le_max_left _ _
  have hu1 : (1 : ℝ) ≤ u := le_max_right _ _
  -- a point where the main term has grown by exactly `1/2`
  obtain ⟨w, hw1, hw2⟩ := ((hlim.eventually_ge_atTop (M u + 1 / 2)).and
    (eventually_ge_atTop u)).exists
  have hcontuw : ContinuousOn M (Set.Icc u w) :=
    hcont.mono (fun z hz => le_trans hu1 hz.1)
  have hsub := intermediate_value_Icc hw2 hcontuw
  have hmem : M u + 1 / 2 ∈ Set.Icc (M u) (M w) := ⟨by linarith, hw1⟩
  obtain ⟨v, hvmem, hv⟩ := hsub hmem
  have hbu : |pi u - M u| < 1 / 4 := by
    obtain ⟨h1, h2, h3⟩ := hU u huU
    have hbb := hb u h2
    rw [hexp] at hbb
    linarith
  have hbv : |pi v - M v| < 1 / 4 := by
    obtain ⟨h1, h2, h3⟩ := hU v (le_trans huU hvmem.1)
    have hbb := hb v h2
    rw [hexp] at hbb
    linarith
  obtain ⟨k1, hk1⟩ := hint u
  obtain ⟨k2, hk2⟩ := hint v
  -- `(π v - π u) - 1/2` is both `< 1/2` and `≥ 1/2` in absolute value
  have hkey : |((k2 - k1 : ℤ) : ℝ) - 1 / 2| < 1 / 2 := by
    have h1 := abs_lt.mp hbu
    have h2 := abs_lt.mp hbv
    rw [hk1] at h1
    rw [hk2] at h2
    rw [abs_lt]
    push_cast
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hfar : (1 : ℝ) / 2 ≤ |((k2 - k1 : ℤ) : ℝ) - 1 / 2| := by
    rcases le_or_gt (k2 - k1) 0 with hk | hk
    · have hle : ((k2 - k1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hge : (1 : ℝ) ≤ ((k2 - k1 : ℤ) : ℝ) := by exact_mod_cast hk
      rw [abs_of_nonneg (by linarith)]
      linarith
  linarith
