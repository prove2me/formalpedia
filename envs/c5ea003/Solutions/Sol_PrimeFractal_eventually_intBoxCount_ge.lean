-- Prove2me | solution 1 for PrimeFractal.eventually_intBoxCount_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:22:14.852571+00:00
-- url     : https://prove2.me/submissions/77b16611-e85d-4cb2-94ce-1bc1b32dc2eb

-- Sol generated from NumberTheory/PrimeFractalIntegers.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalIntegers
import Theorems.Thm_PrimeFractal_eventually_log_pow_le
import Theorems.Thm_PrimeFractal_eventually_two_le_log
import Theorems.Thm_PrimeFractal_sub_one_le_intBoxCount

/-!
# The logarithmic lens cannot see primality

The same construction applied to *all* integers `≥ 2` produces the "integer
fractal" `{1 / log n : n ≥ 2}`.  We show it has

* Hausdorff dimension `0` (it is countable), and
* box-counting dimension `1` (`tendsto_intBoxCount_log_div`),

exactly like the prime fractal.  The proof of the lower bound is the same
separation estimate `boxIndex_lt`, but with no arithmetic input at all: for
integers one may simply count `Y - 1` of them below `Y`, where the primes needed
Chebyshev's theorem.

**Conclusion.** Both dimensions agree for the primes and for all integers, so
neither can detect primality: the mission's programme of reading off arithmetic
information (twin primes) from `dim (P, d)` is structurally impossible.  The
difference between the two sets is only visible in the second-order term (the
number of occupied boxes; see `NumberTheory.PrimeFractalRefined`).
-/

open PrimeFractal

open Filter Topology













open PrimeFractal in
theorem solution:
    ∀ᶠ m : ℕ in atTop, (m : ℝ) / (4 * (Real.log m) ^ 3) ≤ (intBoxCount m : ℝ) := by
  filter_upwards [eventually_log_pow_le (C := 16) (by norm_num) 3, eventually_two_le_log]
    with m h16 hL2
  set L : ℝ := Real.log m with hLdef
  have hL0 : 0 < L := by linarith
  have hL8 : (8 : ℝ) ≤ L ^ 3 := by nlinarith [hL2, sq_nonneg (L - 2), sq_nonneg (L + 2)]
  have hL3 : (0 : ℝ) < L ^ 3 := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set Y : ℕ := ⌊(m : ℝ) / L ^ 3⌋₊ with hYdef
  have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
  have hYle : (Y : ℝ) * L ^ 3 ≤ (m : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (m : ℝ) / L ^ 3 by positivity)
    rw [← hYdef] at h
    rw [← le_div_iff₀ hL3]
    exact h
  have hYgt : (m : ℝ) < ((Y : ℝ) + 1) * L ^ 3 := by
    have h := Nat.lt_floor_add_one ((m : ℝ) / L ^ 3)
    rw [← hYdef] at h
    rw [← div_lt_iff₀ hL3]
    exact h
  have hmL16 : (16 : ℝ) * L ^ 3 ≤ (m : ℝ) := by linarith
  have hY15 : (15 : ℝ) ≤ (Y : ℝ) := by nlinarith [hYgt, hmL16, hL3]
  have hYm : (Y : ℝ) ≤ (m : ℝ) := by nlinarith [hYle, hL8, hY0]
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogYL : Real.log Y ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by linarith) hYm
  have hsep : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ (m : ℝ) := by
    have h1 : (Real.log Y) ^ 2 ≤ L ^ 2 := by nlinarith
    have h2 : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ 2 * (Y : ℝ) * L ^ 2 := by nlinarith
    have h3 : 2 * (Y : ℝ) * L ^ 2 ≤ (Y : ℝ) * L ^ 3 := by nlinarith [sq_nonneg L, hY0, hL2]
    linarith
  have hcount : (Y - 1 : ℕ) ≤ intBoxCount m := sub_one_le_intBoxCount hsep
  have hcount' : (Y : ℝ) - 1 ≤ (intBoxCount m : ℝ) := by
    have hY1 : 1 ≤ Y := by exact_mod_cast le_trans (by norm_num : (1 : ℝ) ≤ 15) hY15
    have : ((Y - 1 : ℕ) : ℝ) ≤ (intBoxCount m : ℝ) := by exact_mod_cast hcount
    rwa [Nat.cast_sub hY1, Nat.cast_one] at this
  -- `m / (4 L^3) ≤ Y - 1`
  have hm2Y : (m : ℝ) ≤ 2 * (Y : ℝ) * L ^ 3 := by nlinarith [hYgt, hY15, hL3]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hcount', hm2Y, hL3, hY15]
