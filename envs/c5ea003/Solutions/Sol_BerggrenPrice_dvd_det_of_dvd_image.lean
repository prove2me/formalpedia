-- Prove2me | solution 1 for BerggrenPrice.dvd_det_of_dvd_image
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:45:26.13028+00:00
-- url     : https://prove2.me/submissions/81300e07-b9e2-45df-bbee-016446690eec

-- Sol generated from Algebra/BerggrenPriceInterlock/Classification.lean
import Mathlib
import Definitions.Def_Algebra_BerggrenPriceInterlock_Trees

/-!
# Berggren–Price interlock, Part VII: what a tree generator can look like

Why is determinant `±2` allowed at all?  Two structural facts explain the interlock:

* `dvd_det_of_dvd_image` — a common divisor of the image of a coprime pair divides the
  determinant.  So a generator of determinant `±1` preserves coprimality for free, while
  a generator of determinant `±2` preserves it only because the parity condition forces
  the gcd to be odd.  This is exactly the gap Price's tree lives in.
* `node_map_parity` — any integer linear map sending nodes to nodes has *odd column
  sums* `a + c` and `b + d`.  Both generator triples satisfy this, and it is what rules
  out the naive "halving" maps such as `(m,n) ↦ (2m−n, n)`.

Together these are the two constraints that any classification of ternary Pythagorean
trees must start from (see `FUTURE_DIRECTIONS.md`, conjecture C4).
-/

open BerggrenPrice




open BerggrenPrice in
theorem solution{a b c d x y k : ℤ} (hxy : IsCoprime x y)
    (h1 : k ∣ a * x + b * y) (h2 : k ∣ c * x + d * y) : k ∣ a * d - b * c := by
  obtain ⟨u, v, huv⟩ := hxy
  have hx : k ∣ (a * d - b * c) * x := by
    have : (a * d - b * c) * x = d * (a * x + b * y) - b * (c * x + d * y) := by ring
    rw [this]
    exact dvd_sub (h1.mul_left d) (h2.mul_left b)
  have hy : k ∣ (a * d - b * c) * y := by
    have : (a * d - b * c) * y = a * (c * x + d * y) - c * (a * x + b * y) := by ring
    rw [this]
    exact dvd_sub (h2.mul_left a) (h1.mul_left c)
  have : (a * d - b * c) = u * ((a * d - b * c) * x) + v * ((a * d - b * c) * y) := by
    linear_combination (a * d - b * c) * huv.symm
  rw [this]
  exact dvd_add (hx.mul_left u) (hy.mul_left v)
