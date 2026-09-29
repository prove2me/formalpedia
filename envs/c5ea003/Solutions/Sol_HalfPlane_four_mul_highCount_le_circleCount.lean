-- Prove2me | solution 1 for HalfPlane.four_mul_highCount_le_circleCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:05:06.145335+00:00
-- url     : https://prove2.me/submissions/ad224e7e-8f02-48f2-a097-6c3dccb54254

-- Sol generated from MachineLearning/HalfPlaneReflection.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCRTSeparable
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneReflection
import Theorems.Thm_HalfPlane_circle_cast_iff
import Theorems.Thm_HalfPlane_circle_reflect_fst
import Theorems.Thm_HalfPlane_mem_circleFinset

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







lemma highCount_eq_card_high (N : ℕ) : highCount N = (highFinset N).card := rfl



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
theorem solution(N : ℕ) (hN : 0 < N) :
    4 * highCount N ≤ circleCount N := by
  haveI : NeZero N := ⟨by omega⟩
  classical
  set Hs := highFinset N with hHs
  set S1 := Hs with hS1
  set S2 := Hs.image (fun p => (N - p.1, N - p.2)) with hS2
  set S3 := Hs.image (fun p => (N - p.1, p.2)) with hS3
  set S4 := Hs.image (fun p => (p.1, N - p.2)) with hS4
  -- coordinate information for each block
  have hmem1 : ∀ p ∈ S1, N < 2 * p.1 ∧ N < 2 * p.2 ∧ p ∈ circleFinset N := by
    intro p hp
    refine ⟨(high_coord_bounds hp).1, (high_coord_bounds hp).2, ?_⟩
    exact Finset.mem_of_mem_filter _ hp
  have hmem2 : ∀ p ∈ S2, 2 * p.1 < N ∧ 2 * p.2 < N ∧ p ∈ circleFinset N := by
    intro p hp
    rw [hS2, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hb := high_coord_bounds hq
    rw [mem_highFinset] at hq
    obtain ⟨⟨h1, h2, hc⟩, hs⟩ := hq
    refine ⟨by omega, by omega, ?_⟩
    rw [mem_circleFinset]
    refine ⟨by omega, by omega, ?_⟩
    rw [circle_reflect_fst (by omega), circle_reflect_snd (by omega)]
    exact hc
  have hmem3 : ∀ p ∈ S3, 2 * p.1 < N ∧ N < 2 * p.2 ∧ p ∈ circleFinset N := by
    intro p hp
    rw [hS3, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hb := high_coord_bounds hq
    rw [mem_highFinset] at hq
    obtain ⟨⟨h1, h2, hc⟩, hs⟩ := hq
    refine ⟨by omega, by omega, ?_⟩
    rw [mem_circleFinset]
    refine ⟨by omega, by omega, ?_⟩
    rw [circle_reflect_fst (by omega)]
    exact hc
  have hmem4 : ∀ p ∈ S4, N < 2 * p.1 ∧ 2 * p.2 < N ∧ p ∈ circleFinset N := by
    intro p hp
    rw [hS4, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hb := high_coord_bounds hq
    rw [mem_highFinset] at hq
    obtain ⟨⟨h1, h2, hc⟩, hs⟩ := hq
    refine ⟨by omega, by omega, ?_⟩
    rw [mem_circleFinset]
    refine ⟨by omega, by omega, ?_⟩
    rw [circle_reflect_snd (by omega)]
    exact hc
  -- all four blocks have the same cardinality
  have hcard2 : S2.card = Hs.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha' := mem_highFinset.mp ha
    have hb' := mem_highFinset.mp hb
    have e1 : N - a.1 = N - b.1 := by simpa using congrArg Prod.fst hab
    have e2 : N - a.2 = N - b.2 := by simpa using congrArg Prod.snd hab
    exact Prod.ext (by omega) (by omega)
  have hcard3 : S3.card = Hs.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha' := mem_highFinset.mp ha
    have hb' := mem_highFinset.mp hb
    have e1 : N - a.1 = N - b.1 := by simpa using congrArg Prod.fst hab
    have e2 : a.2 = b.2 := by simpa using congrArg Prod.snd hab
    exact Prod.ext (by omega) e2
  have hcard4 : S4.card = Hs.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have ha' := mem_highFinset.mp ha
    have hb' := mem_highFinset.mp hb
    have e1 : a.1 = b.1 := by simpa using congrArg Prod.fst hab
    have e2 : N - a.2 = N - b.2 := by simpa using congrArg Prod.snd hab
    exact Prod.ext e1 (by omega)
  -- pairwise disjointness, read off from the coordinate information
  have d12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    have := hmem1 p h1; have := hmem2 p h2; omega
  have d13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]; intro p h1 h3
    have := hmem1 p h1; have := hmem3 p h3; omega
  have d14 : Disjoint S1 S4 := by
    rw [Finset.disjoint_left]; intro p h1 h4
    have := hmem1 p h1; have := hmem4 p h4; omega
  have d23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]; intro p h2 h3
    have := hmem2 p h2; have := hmem3 p h3; omega
  have d24 : Disjoint S2 S4 := by
    rw [Finset.disjoint_left]; intro p h2 h4
    have := hmem2 p h2; have := hmem4 p h4; omega
  have d34 : Disjoint S3 S4 := by
    rw [Finset.disjoint_left]; intro p h3 h4
    have := hmem3 p h3; have := hmem4 p h4; omega
  have hsub : S1 ∪ S2 ∪ S3 ∪ S4 ⊆ circleFinset N := by
    intro p hp
    simp only [Finset.mem_union] at hp
    rcases hp with ((h | h) | h) | h
    · exact (hmem1 p h).2.2
    · exact (hmem2 p h).2.2
    · exact (hmem3 p h).2.2
    · exact (hmem4 p h).2.2
  have hcardU : (S1 ∪ S2 ∪ S3 ∪ S4).card = 4 * Hs.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint d12, hcard2, hcard3, hcard4]
    · ring
    · rw [Finset.disjoint_union_left]; exact ⟨d13, d23⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨d14, d24⟩, d34⟩
  calc 4 * highCount N = (S1 ∪ S2 ∪ S3 ∪ S4).card := by
        rw [hcardU, highCount_eq_card_high]
    _ ≤ (circleFinset N).card := Finset.card_le_card hsub
    _ = circleCount N := rfl
