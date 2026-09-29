-- Prove2me | solution 1 for ThreeCubes.card_cubeTripleValues
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:25:29.518012+00:00
-- url     : https://prove2.me/submissions/71134621-e3b6-431c-84fc-a9f762e09c0a

-- Sol generated from Probability/LowerBoundsSharp.lean
import Mathlib
import Definitions.Def_Probability_LowerBounds
import Definitions.Def_Probability_LowerBoundsSharp
import Theorems.Thm_ThreeCubes_cube_gap_decode

/-!
# A sharper unconditional lower bound: `repCount N ≫ N^{19/27}`

`Probability.ThreeCubes.LowerBounds` counts the values `k³ + m³` of a *two*-parameter family
and obtains `repCount N ≫ N^{5/9} = N^{15/27}`.  The bottleneck there is that the third cube is
never used: the small cube `m³` must stay below the gap `(k+1)³ - k³ ≍ k^{2/3·3}`, so
`m ≍ k^{2/3}` and one gets `k · k^{2/3} = k^{5/3}` values below `k³`.

Here we iterate the gap trick once more.  Take

* `x ∈ [8K⁹, 16K⁹)`,
* `y ∈ [2K⁶, 4K⁶)`,
* `z ∈ [K⁴, 2K⁴)`,

so that `y³ + z³` is below the cube gap at `x` **and** `z³` is below the cube gap at `y`.  Then
the value `n = x³ + y³ + z³` determines `x = ⌊n^{1/3}⌋`, then `y = ⌊(n - x³)^{1/3}⌋`, then `z`:
the parametrisation is injective (`ThreeCubes.cube_triple_inj`).  Counting,

`16 K¹⁹` distinct sums of three cubes lie in `[0, 4168 K²⁷]`,

which is the power saving `N^{19/27} = N^{0.7037…}`, a genuine improvement on `N^{5/9}` and
now quite close to the *upper* density `7/9` of `ThreeCubes.card_isSumOfThreeCubes_le`.

The exponents produced by nesting the gap trick over `r` cubes are
`1 - (2/3)^r`: the boxes have sizes `A`, `A^{2/3}`, `A^{4/9}`, …, `A^{(2/3)^{r-1}}`, so they
contain `A^{3(1-(2/3)^r)}` triples with values up to `A³`.  For `r = 2` this is `5/9`
(the bound of `LowerBounds`) and for `r = 3` it is `19/27` — and `r = 3` is the end of the
line for *three* cubes, so `19/27` is exactly the limit of the elementary gap method here.
Going beyond it requires bounding the multiplicity of representations rather than merely
constructing injective boxes.

Main results.

* `ThreeCubes.cube_gap_decode` — the decoding step: if a remainder is below the cube gap then
  the leading cube is determined.
* `ThreeCubes.cube_triple_inj` — injectivity of `(x, y, z) ↦ x³ + y³ + z³` on the boxes above.
* `ThreeCubes.repCount_ge_nineteen` — `16 K¹⁹ ≤ repCount (4168 K²⁷)`.
* `ThreeCubes.repCount_rpow_ge` — the same in real-exponent form:
  `N^{19/27} ≤ 23 · repCount N` for `N = 4168 K²⁷`.
-/

open ThreeCubes

open Finset

/-! ### The decoding step -/


/-! ### The three boxes and their gap inequalities -/

/-- On the box `y < 4K⁶`, `z < 2K⁴`, `8K⁹ ≤ x`, the pair `y³ + z³` is below the cube gap
at `x`. -/
theorem gap_bound_outer {K x y z : ℕ} (hx : 8 * K ^ 9 ≤ x) (hy : y < 4 * K ^ 6)
    (hz : z < 2 * K ^ 4) : y ^ 3 + z ^ 3 < 3 * x ^ 2 + 3 * x + 1 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · norm_num at hy
  have hy3 : y ^ 3 ≤ (4 * K ^ 6) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hz3 : z ^ 3 ≤ (2 * K ^ 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hx2 : (8 * K ^ 9) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hx 2
  have e1 : (4 * K ^ 6) ^ 3 = 64 * K ^ 18 := by ring
  have e2 : (2 * K ^ 4) ^ 3 = 8 * K ^ 12 := by ring
  have e3 : (8 * K ^ 9) ^ 2 = 64 * K ^ 18 := by ring
  have e4 : K ^ 12 ≤ K ^ 18 := Nat.pow_le_pow_right hK (by norm_num)
  omega

/-- On the box `2K⁶ ≤ y`, `z < 2K⁴`, the cube `z³` is below the cube gap at `y`. -/
theorem gap_bound_inner {K y z : ℕ} (hy : 2 * K ^ 6 ≤ y) (hz : z < 2 * K ^ 4) :
    z ^ 3 < 3 * y ^ 2 + 3 * y + 1 := by
  have hz3 : z ^ 3 ≤ (2 * K ^ 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hy2 : (2 * K ^ 6) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hy 2
  have e1 : (2 * K ^ 4) ^ 3 = 8 * K ^ 12 := by ring
  have e2 : (2 * K ^ 6) ^ 2 = 4 * K ^ 12 := by ring
  omega

/-- **Injectivity of the three-parameter family.**  On the boxes `8K⁹ ≤ x < 16K⁹`,
`2K⁶ ≤ y < 4K⁶`, `K⁴ ≤ z < 2K⁴` the map `(x, y, z) ↦ x³ + y³ + z³` is injective. -/
theorem cube_triple_inj {K x y z x' y' z' : ℕ}
    (hx : 8 * K ^ 9 ≤ x) (hy : 2 * K ^ 6 ≤ y) (hy2 : y < 4 * K ^ 6) (hz : z < 2 * K ^ 4)
    (hx' : 8 * K ^ 9 ≤ x') (hy' : 2 * K ^ 6 ≤ y') (hy2' : y' < 4 * K ^ 6)
    (hz' : z' < 2 * K ^ 4)
    (h : x ^ 3 + y ^ 3 + z ^ 3 = x' ^ 3 + y' ^ 3 + z' ^ 3) : x = x' ∧ y = y' ∧ z = z' := by
  obtain ⟨hxx, hrest⟩ := cube_gap_decode (gap_bound_outer hx hy2 hz)
    (gap_bound_outer hx' hy2' hz') (by omega)
  obtain ⟨hyy, hzz⟩ := cube_gap_decode (gap_bound_inner hy hz) (gap_bound_inner hy' hz') hrest
  exact ⟨hxx, hyy, Nat.pow_left_injective (by norm_num) hzz⟩

/-! ### The counting -/









open ThreeCubes in
theorem solution(K : ℕ) : (cubeTripleValues K).card = 16 * K ^ 19 := by
  rw [cubeTripleValues, Finset.card_image_of_injOn]
  · rw [Finset.card_product, Finset.card_product, Nat.card_Ico, Nat.card_Ico, Nat.card_Ico]
    have h1 : 16 * K ^ 9 - 8 * K ^ 9 = 8 * K ^ 9 := by omega
    have h2 : 4 * K ^ 6 - 2 * K ^ 6 = 2 * K ^ 6 := by omega
    have h3 : 2 * K ^ 4 - K ^ 4 = K ^ 4 := by omega
    rw [h1, h2, h3]
    ring
  · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hq h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico] at hp hq
    obtain ⟨⟨hx1, -⟩, ⟨hy1, hy2⟩, -, hz2⟩ := hp
    obtain ⟨⟨hx1', -⟩, ⟨hy1', hy2'⟩, -, hz2'⟩ := hq
    have h' : x ^ 3 + y ^ 3 + z ^ 3 = x' ^ 3 + y' ^ 3 + z' ^ 3 := h
    obtain ⟨e1, e2, e3⟩ := cube_triple_inj hx1 hy1 hy2 hz2 hx1' hy1' hy2' hz2' h'
    simp [e1, e2, e3]
