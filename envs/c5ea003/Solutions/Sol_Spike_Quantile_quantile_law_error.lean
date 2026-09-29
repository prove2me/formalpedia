-- Prove2me | solution 1 for Spike.Quantile.quantile_law_error
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:09:09.332458+00:00
-- url     : https://prove2.me/submissions/e1674e44-deb1-4f54-93ee-51bff82ddcb9

-- Sol generated from Probability/SpikeQuantileLimitLaw.lean
import Mathlib
import Definitions.Def_Probability_SpikeInclusionGeometry
import Definitions.Def_Probability_SpikeQuantileIdentity
import Definitions.Def_Probability_SpikeQuantileLimitLaw
import Theorems.Thm_Spike_Quantile_card_sublevel

/-!
# The continuum quantile law of the window residue

`Catalog/Probability/SpikeQuantileIdentity.lean` proves the exact discrete
quantile identity

`#{ j ∈ W N : residue N j ≤ x } = min (3 isqrt N) (isqrt (N + x)) - isqrt N`.

This file closes the remaining, *asymptotic* half of future direction 1: the
limit law of the rescaled residue `v / s²` under the uniform position law on the
window.  Everything is proved with an explicit, non-asymptotic error term, so the
limit statement is a corollary rather than the primitive result.

Main results (`Spike.Quantile`):

* `card_sublevel_sq` : on a perfect-square modulus `N = M²` (where the integer
  and real square roots agree, so no rounding of the anchor occurs) the sublevel
  count is exactly `isqrt (M² + x) - M` as long as `x ≤ 8 M²`, i.e. as long as
  the threshold stays inside the window;
* `quantile_law_error` : the **Kolmogorov distance bound**
  `| F_M(x) - (√(1 + x/M²) - 1)/2 | ≤ 1/(2M)`
  where `F_M(x)` is the empirical fraction of window positions with residue at
  most `x`.  The limit c.d.f. `y ↦ (√(1+y) - 1)/2` is precisely the law of
  `(1 + 2U)² - 1` for `U` uniform on `[0,1]`, which is the conjectured law;
* `quantile_tendsto` : consequently, for every level `y ∈ [0,8]` the empirical
  fraction below `y M²` converges to `(√(1+y) - 1)/2`;
* `decile_law_exact` : at the round-85 decile level `y = 11/25` the limit law
  returns exactly `1/10`, and on the divisible moduli `N = (5m)²` the empirical
  fraction *equals* `1/10` with no error at all — the decile statistic and the
  magnitude statistic agree exactly, not just in the limit.

Interpretation: a first-decile analysis on this window is a `v ≤ 0.44 s²`
analysis with an error of at most one position, at every scale.  There is no
asymptotic regime in which the positional cut carries information beyond the
magnitude cut.
-/

open Spike.Quantile

open Spike Filter

/-! ### Comparison of the integer and real square roots -/

/-- The integer square root never exceeds the real one. -/
theorem natSqrt_le_sqrt (m : ℕ) : (Nat.sqrt m : ℝ) ≤ Real.sqrt m := by
  have h : ((Nat.sqrt m : ℝ)) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m : ℝ)), Real.sqrt_nonneg (m : ℝ),
    Nat.cast_nonneg (α := ℝ) (Nat.sqrt m)]

/-- The real square root is less than one more than the integer one. -/
theorem sqrt_lt_natSqrt_succ (m : ℕ) : Real.sqrt m < (Nat.sqrt m : ℝ) + 1 := by
  have h0 : m < (Nat.sqrt m + 1) ^ 2 := by simpa [pow_two] using Nat.lt_succ_sqrt' m
  have h : (m : ℝ) < ((Nat.sqrt m : ℝ) + 1) ^ 2 := by exact_mod_cast h0
  nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m : ℝ)), Real.sqrt_nonneg (m : ℝ),
    Nat.cast_nonneg (α := ℝ) (Nat.sqrt m)]

/-- The rounding error of the integer square root, in the form used below. -/
theorem abs_natSqrt_sub_sqrt_le (m : ℕ) : |(Nat.sqrt m : ℝ) - Real.sqrt m| ≤ 1 := by
  have h1 := natSqrt_le_sqrt m
  have h2 := sqrt_lt_natSqrt_succ m
  rw [abs_le]
  constructor <;> linarith

/-! ### The exact sublevel count on a perfect-square modulus -/


/-- **Exact sublevel count.**  For a threshold inside the window
(`x ≤ 8 M²`) the number of window positions with residue at most `x` is
`isqrt (M² + x) - M`. -/
theorem card_sublevel_sq (M x : ℕ) (hx : x ≤ 8 * M ^ 2) :
    ((window (M ^ 2)).filter (fun j => residue (M ^ 2) j ≤ x)).card
      = Nat.sqrt (M ^ 2 + x) - M := by
  have h1 : Nat.sqrt (M ^ 2) = M := Nat.sqrt_eq' M
  have h2 : Nat.sqrt (M ^ 2 + x) ≤ 3 * M := by
    have hle : M ^ 2 + x ≤ (3 * M) ^ 2 := by nlinarith
    calc Nat.sqrt (M ^ 2 + x) ≤ Nat.sqrt ((3 * M) ^ 2) := Nat.sqrt_le_sqrt hle
      _ = 3 * M := Nat.sqrt_eq' _
  rw [card_sublevel (N := M ^ 2) x, h1]
  omega

/-- The anchor bound: the sublevel count is nonnegative in the integers. -/
theorem le_natSqrt_add (M x : ℕ) : M ≤ Nat.sqrt (M ^ 2 + x) := by
  have := Nat.sqrt_le_sqrt (Nat.le_add_right (M ^ 2) x)
  rwa [Nat.sqrt_eq' M] at this

/-! ### The limit law, with an explicit error term -/



/-- Rewriting the limit c.d.f. at the rescaled threshold. -/
theorem limitCDF_eq (M x : ℕ) (hM : 0 < M) :
    limitCDF ((x : ℝ) / (M : ℝ) ^ 2)
      = (Real.sqrt ((M : ℝ) ^ 2 + x) - M) / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h : (1 + (x : ℝ) / (M : ℝ) ^ 2) = ((M : ℝ) ^ 2 + x) / (M : ℝ) ^ 2 := by field_simp
  rw [limitCDF, h, Real.sqrt_div (by positivity), Real.sqrt_sq hM'.le]
  field_simp



/-! ### The decile point: the limit law is attained exactly -/




open Spike.Quantile in
theorem solution(M x : ℕ) (hM : 0 < M) (hx : x ≤ 8 * M ^ 2) :
    |empFrac M x - limitCDF ((x : ℝ) / (M : ℝ) ^ 2)| ≤ 1 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard := card_sublevel_sq M x hx
  have hle := le_natSqrt_add M x
  have hcast : (((window (M ^ 2)).filter (fun j => residue (M ^ 2) j ≤ x)).card : ℝ)
      = (Nat.sqrt (M ^ 2 + x) : ℝ) - (M : ℝ) := by
    rw [hcard, Nat.cast_sub hle]
  have hreal : Real.sqrt ((M : ℝ) ^ 2 + x) = Real.sqrt ((M ^ 2 + x : ℕ) : ℝ) := by
    push_cast; ring_nf
  have herr : |(Nat.sqrt (M ^ 2 + x) : ℝ) - Real.sqrt ((M : ℝ) ^ 2 + x)| ≤ 1 := by
    rw [hreal]; exact abs_natSqrt_sub_sqrt_le _
  rw [empFrac, hcast, limitCDF_eq M x hM, div_sub_div_same]
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * (M : ℝ))]
  have hnum : |(Nat.sqrt (M ^ 2 + x) : ℝ) - (M : ℝ) - (Real.sqrt ((M : ℝ) ^ 2 + x) - M)| ≤ 1 := by
    rw [show (Nat.sqrt (M ^ 2 + x) : ℝ) - (M : ℝ) - (Real.sqrt ((M : ℝ) ^ 2 + x) - M)
        = (Nat.sqrt (M ^ 2 + x) : ℝ) - Real.sqrt ((M : ℝ) ^ 2 + x) by ring]
    exact herr
  gcongr
