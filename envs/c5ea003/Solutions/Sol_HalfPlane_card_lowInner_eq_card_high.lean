-- Prove2me | solution 1 for HalfPlane.card_lowInner_eq_card_high
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:02:20.168541+00:00
-- url     : https://prove2.me/submissions/eff774d1-dcc7-4c4c-a90c-1d1504a249f9

-- Sol generated from MachineLearning/HalfPlaneReflection.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Theorems.Thm_HalfPlane_circle_cast_iff
import Theorems.Thm_HalfPlane_circle_reflect_fst
import Theorems.Thm_HalfPlane_mem_circleFinset
import Theorems.Thm_HalfPlane_mem_lowFinset

/-!
# The half-plane cut: reflection identity, quadrant bound, and non-separability

The cut `x + y < N/2` uses the *integer* sum of the representatives and is therefore
**not** a CRT-separable condition.  Nevertheless the count `H(N)` is rigidly
controlled by the reflection symmetries of the circle:

* `halfPlaneCount_eq_highCount_add` :
  `H(N) = high(N) + 2 · R(N)` for `N ≥ 2`, where `high(N)` counts the circle points
  in the *opposite* corner `x + y > 3N/2` and `R(N)` is the number of square roots
  of `1` below `N/2` (the "axis" points `(0, u)` and `(u, 0)`).
  The bijection is the antipodal map `(x, y) ↦ (N - x, N - y)`.

* `four_mul_highCount_le_circleCount` :
  `4 · high(N) ≤ C(N)`, via four pairwise disjoint copies of the corner
  produced by the reflection group `⟨x ↦ N - x, y ↦ N - y⟩`.

* `four_mul_halfPlaneCount_le` :
  `4 · H(N) ≤ C(N) + 8 · R(N)`, i.e. `H` is at most a quarter of the circle count
  up to the (tiny, `2^ω(N)`-sized) square-root-of-unity correction.

* `halfPlaneCount_not_multiplicative` : `H` is **not** CRT-separable:
  `H(35) = 6 ≠ 4 = H(5) · H(7)`, while `C(35) = C(5) · C(7)`.
  This is the formal statement of the "classification boundary".
-/

open HalfPlane

open Finset

/-! ### The low, high, inner and axis parts of the circle -/










lemma mem_highFinset {N : ℕ} {p : ℕ × ℕ} :
    p ∈ highFinset N ↔ (p.1 < N ∧ p.2 < N ∧ (p.1 ^ 2 + p.2 ^ 2) % N = 1 % N)
      ∧ 3 * N < 2 * (p.1 + p.2) := by
  simp [highFinset, Finset.mem_filter, mem_circleFinset]

/-! ### Reflecting one coordinate preserves the circle -/


lemma circle_reflect_snd {N a b : ℕ} [NeZero N] (hb : b ≤ N) :
    ((a ^ 2 + (N - b) ^ 2) % N = 1 % N) ↔ ((a ^ 2 + b ^ 2) % N = 1 % N) := by
  rw [circle_cast_iff, circle_cast_iff]
  have hcast : ((N - b : ℕ) : ZMod N) = -(b : ZMod N) := by
    rw [Nat.cast_sub hb]
    simp
  rw [hcast]
  ring_nf

/-! ### The antipodal bijection between the inner low set and the high corner -/

/-- Points of the high corner have both coordinates above `N/2`. -/
lemma high_coord_bounds {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ highFinset N) :
    N < 2 * p.1 ∧ N < 2 * p.2 := by
  rw [mem_highFinset] at hp
  obtain ⟨⟨h1, h2, _⟩, h3⟩ := hp
  omega


/-! ### The axis part -/


/-! ### The reflection identity -/


/-! ### The quadrant bound -/



/-! ### Non-separability of the half-plane count

The circle count is a product of local factors; the half-plane count is not. -/




/-! ### Lab notes: the reflection identity in action

```
N        : 15  16  17  20  21  24  25  28  33  35
H(N)     :  4   6   3   6   4  12   6  10   8   6
high(N)  :  0   2   1   2   0   4   4   6   4   2
R(N)     :  2   2   1   2   2   4   1   2   2   2
4·high   :  0   8   4   8   0  16  16  24  16   8
C(N)     : 16  32  16  32  32  64  20  64  48  32
```
Each column satisfies `H = high + 2R` and `4·high ≤ C`.
-/

example : halfPlaneCount 24 = highCount 24 + 2 * unitRootCount 24 := by decide
example : 4 * highCount 28 ≤ circleCount 28 := by decide


open HalfPlane in
theorem solution(N : ℕ) [NeZero N] :
    (lowInner N).card = (highFinset N).card := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.card_bij'
    (fun p _ => (N - p.1, N - p.2))
    (fun p _ => (N - p.1, N - p.2))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [lowInner, Finset.mem_filter, mem_lowFinset] at hp
    obtain ⟨⟨⟨h1, h2, hc⟩, hs⟩, hx1, hy1⟩ := hp
    rw [mem_highFinset]
    dsimp only
    refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
    rw [circle_reflect_fst (by omega), circle_reflect_snd (by omega)]
    exact hc
  · intro p hp
    have hb := high_coord_bounds hp
    rw [mem_highFinset] at hp
    obtain ⟨⟨h1, h2, hc⟩, hs⟩ := hp
    simp only [lowInner, Finset.mem_filter, mem_lowFinset]
    refine ⟨⟨⟨by omega, by omega, ?_⟩, by omega⟩, by omega, by omega⟩
    rw [circle_reflect_fst (by omega), circle_reflect_snd (by omega)]
    exact hc
  · intro p hp
    simp only [lowInner, Finset.mem_filter, mem_lowFinset] at hp
    obtain ⟨⟨⟨h1, h2, _⟩, _⟩, _, _⟩ := hp
    exact Prod.ext (by simp; omega) (by simp; omega)
  · intro p hp
    rw [mem_highFinset] at hp
    obtain ⟨⟨h1, h2, _⟩, _⟩ := hp
    exact Prod.ext (by simp; omega) (by simp; omega)
