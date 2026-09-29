-- Prove2me | solution 1 for PrimeFractal.boxIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:11:43.101554+00:00
-- url     : https://prove2.me/submissions/3fbf3fcd-8039-4a4f-b62f-e409497eca40

-- Sol generated from NumberTheory/PrimeFractalBoxDimension.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Theorems.Thm_PrimeFractal_log_sub_log_ge

/-!
# The box-counting dimension of the prime fractal is exactly `1`

`NumberTheory.PrimeFractalHausdorff` shows that the Hausdorff dimension of the
prime fractal `{1 / log p : p prime} ⊆ ℝ` is `0`, refuting the mission
conjecture.  Here we prove the *positive* half of the story: the notion that
actually sees the conjectured value is the **box-counting (Minkowski)
dimension**, and for the prime fractal it equals `1` on the nose.

At scale `1/m` we count the boxes `[k/m, (k+1)/m)` that meet the prime fractal,
i.e. the cardinality `boxCount m` of the set of values `⌊m / log p⌋` over primes
`p`.  The two halves are:

* `boxCount_le` : `boxCount m ≤ 2m + 1` — a trivial upper bound valid for any
  subset of an interval, which is what forces the dimension to be `≤ 1`.  In
  particular *no* configuration of primes — twin primes included — can produce
  a dimension `1 + ε` with `ε > 0`.
* `eventually_boxCount_ge` : `boxCount m ≥ m / (16 (log m)^4)`.  This is the
  arithmetic input: it uses the Chebyshev-type lower bound
  `PrimeFractal.le_primeCounting_mul_log` together with the observation that
  `p ↦ ⌊m / log p⌋` is injective on primes `p ≤ Y` as soon as
  `2 Y (log Y)^2 ≤ m` (primes below `Y` are spread more than `1/m` apart in the
  `d`-metric).

Together they give `tendsto_boxCount_log_div`: `log (boxCount m) / log m → 1`,
hence `upperBoxDim = lowerBoxDim = 1` (`upperBoxDim_eq_one`,
`lowerBoxDim_eq_one`), while the Hausdorff dimension is `0`
(`dimH_lt_boxDim`).  The prime fractal is therefore a *dimension-irregular*
set: box and Hausdorff dimensions disagree maximally.
-/

open PrimeFractal

open Filter Topology




/-! ### Elementary bounds -/







/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/














open PrimeFractal in
theorem solution{m Y p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hpY : p ≤ Y) (hqY : q ≤ Y)
    (hlt : p < q) (hm : 2 * (Y : ℝ) * (Real.log Y) ^ 2 ≤ m) :
    boxIndex m q < boxIndex m p := by
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpq' : (p : ℝ) < (q : ℝ) := by exact_mod_cast hlt
  set a : ℝ := Real.log p with ha
  set b : ℝ := Real.log q with hb
  set L : ℝ := Real.log Y with hL
  have ha0 : 0 < a := Real.log_pos (by linarith)
  have hab : a < b := Real.log_lt_log (by linarith) hpq'
  have hb0 : 0 < b := lt_trans ha0 hab
  have hbL : b ≤ L := Real.log_le_log (by linarith) (by exact_mod_cast hqY)
  have haL : a ≤ L := le_of_lt (lt_of_lt_of_le hab hbL)
  have hL0 : 0 < L := lt_of_lt_of_le ha0 haL
  have hsep : 1 / (2 * (p : ℝ)) ≤ b - a := log_sub_log_ge hp hlt
  have hPY : (p : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hpY
  have habL : a * b ≤ L ^ 2 := by nlinarith
  have hmP : 2 * (p : ℝ) * (a * b) ≤ (m : ℝ) := by nlinarith
  -- `m * (1/a - 1/b) ≥ 1`
  have hstep : 1 ≤ (m : ℝ) * (1 / a - 1 / b) := by
    have hdiff : 1 / a - 1 / b = (b - a) / (a * b) := by
      field_simp
    rw [hdiff, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    have hP0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : 2 * (p : ℝ) * (b - a) ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (by positivity)]
      simpa [one_div] using hsep
    nlinarith [hmP, h1, mul_pos ha0 hb0]
  have hqnn : 0 ≤ (m : ℝ) * logInv q := by
    have : 0 ≤ logInv q := le_of_lt (by
      have : 0 < Real.log q := hb0
      simpa [logInv] using one_div_pos.mpr this)
    positivity
  have hge : (m : ℝ) * logInv q + 1 ≤ (m : ℝ) * logInv p := by
    simp only [logInv]
    nlinarith [hstep]
  have hfl := Nat.floor_le_floor hge
  rw [Nat.floor_add_one hqnn] at hfl
  simp only [boxIndex]
  exact Nat.lt_of_succ_le hfl
