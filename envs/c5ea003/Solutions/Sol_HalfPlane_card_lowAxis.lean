-- Prove2me | solution 1 for HalfPlane.card_lowAxis
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:58:54.620078+00:00
-- url     : https://prove2.me/submissions/47bb629a-e5b0-4881-87d5-c6cd1850473e

-- Sol generated from MachineLearning/HalfPlaneReflection.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Theorems.Thm_HalfPlane_mem_lowFinset
import Theorems.Thm_HalfPlane_unitRootCount_eq_card

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











/-! ### Reflecting one coordinate preserves the circle -/



/-! ### The antipodal bijection between the inner low set and the high corner -/



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
theorem solution(N : ℕ) (hN : 2 ≤ N) :
    (lowAxis N).card = 2 * unitRootCount N := by
  classical
  have hsplit : lowAxis N =
      (unitRootFinset N).image (fun u => ((0 : ℕ), u))
        ∪ (unitRootFinset N).image (fun u => (u, (0 : ℕ))) := by
    ext p
    simp only [lowAxis, Finset.mem_filter, mem_lowFinset, Finset.mem_union,
      Finset.mem_image, unitRootFinset, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨h1, h2, hc⟩, hs⟩, hax⟩
      rcases Nat.eq_zero_or_pos p.1 with hx | hx
      · left
        refine ⟨p.2, ⟨h2, by omega, ?_⟩, ?_⟩
        · rw [hx] at hc; simpa using hc
        · exact Prod.ext (by simpa using hx.symm) rfl
      · have hy : p.2 = 0 := by omega
        right
        refine ⟨p.1, ⟨h1, by omega, ?_⟩, ?_⟩
        · rw [hy] at hc; simpa using hc
        · exact Prod.ext rfl (by simpa using hy.symm)
    · rintro (⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩ | ⟨u, ⟨hu1, hu2, hu3⟩, rfl⟩)
      · exact ⟨⟨⟨by omega, hu1, by simpa using hu3⟩, by simpa using hu2⟩, by simp⟩
      · exact ⟨⟨⟨hu1, by omega, by simpa using hu3⟩, by simpa using hu2⟩, by simp⟩
  have hdisj : Disjoint ((unitRootFinset N).image (fun u => ((0 : ℕ), u)))
      ((unitRootFinset N).image (fun u => (u, (0 : ℕ)))) := by
    rw [Finset.disjoint_left]
    rintro p hp hq
    simp only [Finset.mem_image, unitRootFinset, Finset.mem_filter, Finset.mem_range] at hp hq
    obtain ⟨u, ⟨_, _, hu⟩, rfl⟩ := hp
    obtain ⟨v, ⟨_, _, hv⟩, hveq⟩ := hq
    have hv0 : v = 0 := by
      have h := congrArg Prod.fst hveq
      simp only at h
      omega
    have h1N : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hv0] at hv
    norm_num [h1N] at hv
  have hinj1 : ((unitRootFinset N).image (fun u => ((0 : ℕ), u))).card
      = (unitRootFinset N).card :=
    Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.snd hab)
  have hinj2 : ((unitRootFinset N).image (fun u => (u, (0 : ℕ)))).card
      = (unitRootFinset N).card :=
    Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab)
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hinj1, hinj2, unitRootCount_eq_card]
  ring
