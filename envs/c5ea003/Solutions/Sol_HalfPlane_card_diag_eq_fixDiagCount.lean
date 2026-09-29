-- Prove2me | solution 1 for HalfPlane.card_diag_eq_fixDiagCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:31:57.949483+00:00
-- url     : https://prove2.me/submissions/f237eb98-3865-4890-a95b-06b9d59b012b

-- Sol generated from MachineLearning/HalfPlaneParity.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneParity
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_mem_lowFinset

/-!
# Cycle 3: the parity of the half-plane count is diagonal-local

The half-plane cut `x + y < N/2` is symmetric under the swap `(x,y) ↦ (y,x)`.
Consequently the parity of the non-separable count `H(N)` is decided entirely by
the *diagonal* solutions `x = y`, i.e. by the square roots of `1/2`:

  `H(N) ≡ #{x < N/4 : 2x² ≡ 1 (mod N)}  (mod 2)`.

Together with the reflection identity `H = high + 2R`, the same congruence holds
for the corner count `high(N)`.  So the non-separable object `H` is locally
determined *modulo 2*: any factor-dependent information it carries lives in its
higher-order bits.

We also record two sharpness facts:

* `exists_eight_mul_highCount_gt` : the constant `4` in `4·high(N) ≤ C(N)` cannot be
  improved to `8` (`N = 9`);
* `highCount_not_multiplicative` : the corner count is genuinely non-separable
  (`high(33) = 4` but `high(3)·high(11) = 0`).
-/

open HalfPlane

open Finset








/-! ### Sharpness and the genuine non-separability of the corner count -/



/-! ### Lab notes (cycle 3)

```
N     :  3  5  7  9 15 16 17 24 25 31 33 35
H(N)  :  2  2  2  4  4  6  3 12  6  7  8  6
diag  :  0  0  0  0  0  0  1  0  0  1  0  0
H mod 2: 0  0  0  0  0  0  1  0  0  1  0  0
```
The parity of `H` tracks the diagonal count exactly (checked by full enumeration
for all `N < 80`).  Note `N = 17`: `2·6² = 72 ≡ 4`, while `x = 3` gives
`2·9 = 18 ≡ 1 (mod 17)` and `4·3 = 12 < 17`, so the diagonal contributes one point
and `H(17) = 3` is odd.
-/

example : halfPlaneCount 17 % 2 = fixDiagCount 17 % 2 := by decide
example : fixDiagCount 17 = 1 := by decide
example : highCount 31 % 2 = 1 := by decide


open HalfPlane in
theorem solution(N : ℕ) :
    ((lowFinset N).filter (fun p => p.1 = p.2)).card = fixDiagCount N := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, mem_lowFinset] at hp
    obtain ⟨⟨⟨h1, h2, hc⟩, hs⟩, hdiag⟩ := hp
    simp only [fixDiagFinset, Finset.mem_filter, Finset.mem_range]
    refine ⟨h1, ?_, by omega⟩
    rw [← hdiag] at hc
    have hdbl : p.1 ^ 2 + p.1 ^ 2 = 2 * p.1 ^ 2 := by ring
    rwa [hdbl] at hc
  · intro p hp q hq hpq
    rw [Finset.mem_filter] at hp hq
    have h1 : p.1 = q.1 := hpq
    have hd1 : p.1 = p.2 := hp.2
    have hd2 : q.1 = q.2 := hq.2
    exact Prod.ext h1 (by omega)
  · intro x hx
    simp only [fixDiagFinset, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have hmem : ((x, x) : ℕ × ℕ) ∈ lowFinset N := by
      rw [mem_lowFinset]
      refine ⟨⟨hx1, hx1, ?_⟩, by simpa using (by omega : 2 * (x + x) < N)⟩
      show (x ^ 2 + x ^ 2) % N = 1 % N
      have hdbl : x ^ 2 + x ^ 2 = 2 * x ^ 2 := by ring
      rw [hdbl]
      exact hx2
    exact ⟨(x, x), Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
