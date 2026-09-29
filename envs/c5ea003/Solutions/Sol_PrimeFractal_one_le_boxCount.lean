-- Prove2me | solution 1 for PrimeFractal.one_le_boxCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:18:55.62185+00:00
-- url     : https://prove2.me/submissions/2641ed93-5bb7-4bf7-9619-59e9cfdeb95b

-- Sol generated from NumberTheory/PrimeFractalBoxDimension.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Theorems.Thm_PrimeFractal_boxIndex_le

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



theorem occupiedBoxes_subset (m : ℕ) : occupiedBoxes m ⊆ ↑(Finset.range (2 * m + 1)) := by
  rintro k ⟨p, hp, rfl⟩
  simp only [Finset.coe_range, Set.mem_Iio]
  exact Nat.lt_succ_of_le (boxIndex_le m p hp.two_le)

theorem occupiedBoxes_finite (m : ℕ) : (occupiedBoxes m).Finite :=
  Set.Finite.subset (Finset.range (2 * m + 1)).finite_toSet (occupiedBoxes_subset m)



/-! ### Separation of primes in the `d`-metric -/




/-! ### From Chebyshev to a lower bound on the box count -/



/-! ### Asymptotics -/














open PrimeFractal in
theorem solution(m : ℕ) : 1 ≤ boxCount m := by
  have hmem : boxIndex m 2 ∈ occupiedBoxes m := ⟨2, Nat.prime_two, rfl⟩
  have hne : (occupiedBoxes m).Nonempty := ⟨_, hmem⟩
  exact (Set.ncard_pos (occupiedBoxes_finite m)).mpr hne
