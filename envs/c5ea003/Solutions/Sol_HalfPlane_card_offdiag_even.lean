-- Prove2me | solution 1 for HalfPlane.card_offdiag_even
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:36:30.522231+00:00
-- url     : https://prove2.me/submissions/652898d9-50e7-4b70-8880-9079a8fb70c5

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



/-- The low half-plane is stable under the swap `(x,y) ↦ (y,x)`. -/
lemma swap_mem_lowFinset {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ lowFinset N) :
    (p.2, p.1) ∈ lowFinset N := by
  rw [mem_lowFinset] at hp ⊢
  obtain ⟨⟨h1, h2, hc⟩, hs⟩ := hp
  refine ⟨⟨h2, h1, ?_⟩, by simpa using (by omega : 2 * (p.2 + p.1) < N)⟩
  show (p.2 ^ 2 + p.1 ^ 2) % N = 1 % N
  have hcomm : p.2 ^ 2 + p.1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by ring
  rw [hcomm]
  exact hc





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
    (((lowFinset N).filter (fun p => ¬ p.1 = p.2)).filter (fun p => p.1 < p.2)).card
      = (((lowFinset N).filter (fun p => ¬ p.1 = p.2)).filter (fun p => ¬ p.1 < p.2)).card := by
  refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp ⊢
    obtain ⟨⟨hmem, hne⟩, hlt⟩ := hp
    refine ⟨⟨swap_mem_lowFinset hmem, ?_⟩, ?_⟩
    · show ¬ (p.2 = p.1)
      omega
    · show ¬ (p.2 < p.1)
      omega
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp ⊢
    obtain ⟨⟨hmem, hne⟩, hlt⟩ := hp
    refine ⟨⟨swap_mem_lowFinset hmem, ?_⟩, ?_⟩
    · show ¬ (p.2 = p.1)
      omega
    · show p.2 < p.1
      omega
  · intro p _; rfl
  · intro p _; rfl
