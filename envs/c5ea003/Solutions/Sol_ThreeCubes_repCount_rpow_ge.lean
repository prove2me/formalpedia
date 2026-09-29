-- Prove2me | solution 1 for ThreeCubes.repCount_rpow_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:03:04.848364+00:00
-- url     : https://prove2.me/submissions/95e7e538-e662-4cb7-81d3-4a40bb78c5c5

-- Sol generated from Probability/LowerBoundsSharp.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_LowerBounds
import Definitions.Def_Probability_LowerBoundsSharp
import Theorems.Thm_ThreeCubes_card_cubeTripleValues
import Theorems.Thm_ThreeCubes_le_of_mem_cubeTripleValues

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




/-! ### The counting -/



/-- Every element of `cubeTripleValues K` is a sum of three cubes. -/
theorem isSumOfThreeCubes_of_mem_cubeTripleValues {K n : ℕ} (h : n ∈ cubeTripleValues K) :
    IsSumOfThreeCubes (n : ℤ) := by
  rw [cubeTripleValues, Finset.mem_image] at h
  obtain ⟨⟨x, y, z⟩, -, rfl⟩ := h
  exact ⟨(x : ℤ), (y : ℤ), (z : ℤ), by push_cast; ring⟩


open scoped Classical in
/-- **The sharper power-saving lower bound.**  At least `16 K¹⁹` of the integers in
`[0, 4168 K²⁷]` are sums of three cubes; equivalently `repCount N ≫ N^{19/27}`.  This improves
the exponent `5/9 = 15/27` of `ThreeCubes.repCount_ge`, and is to be compared with the upper
bound `7N/9` of `ThreeCubes.card_isSumOfThreeCubes_le`. -/
theorem repCount_ge_nineteen (K : ℕ) : 16 * K ^ 19 ≤ repCount (4168 * K ^ 27) := by
  have hsub : cubeTripleValues K ⊆
      Finset.filter (fun i : ℕ => IsSumOfThreeCubes (i : ℤ))
        (Finset.range (4168 * K ^ 27 + 1)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := le_of_mem_cubeTripleValues hn; omega,
      isSumOfThreeCubes_of_mem_cubeTripleValues hn⟩
  have hcard := Finset.card_le_card hsub
  rw [card_cubeTripleValues] at hcard
  exact hcard




open ThreeCubes in
open scoped Classical in
theorem solution(K : ℕ) :
    ((4168 * K ^ 27 : ℕ) : ℝ) ^ ((19 : ℝ) / 27) ≤ 23 * repCount (4168 * K ^ 27) := by
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hcast : ((4168 * K ^ 27 : ℕ) : ℝ) = 4168 * (K : ℝ) ^ (27 : ℕ) := by push_cast; ring
  have hsplit : (4168 * (K : ℝ) ^ (27 : ℕ)) ^ ((19 : ℝ) / 27)
      = (4168 : ℝ) ^ ((19 : ℝ) / 27) * (K : ℝ) ^ (19 : ℕ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (K : ℝ) 27,
      ← Real.rpow_natCast (K : ℝ) 19, ← Real.rpow_mul hK0]
    norm_num
  have hnn : (0 : ℝ) ≤ (4168 : ℝ) ^ ((19 : ℝ) / 27) := Real.rpow_nonneg (by norm_num) _
  have h27 : ((4168 : ℝ) ^ ((19 : ℝ) / 27)) ^ (27 : ℕ) = (4168 : ℝ) ^ (19 : ℕ) := by
    rw [← Real.rpow_natCast ((4168 : ℝ) ^ ((19 : ℝ) / 27)) 27, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (4168 : ℝ) 19]
    norm_num
  have hpow : ((4168 : ℝ) ^ ((19 : ℝ) / 27)) ^ (27 : ℕ) ≤ (368 : ℝ) ^ (27 : ℕ) := by
    rw [h27]
    have : (4168 : ℕ) ^ 19 ≤ (368 : ℕ) ^ 27 := by norm_num
    exact_mod_cast this
  have hconst : (4168 : ℝ) ^ ((19 : ℝ) / 27) ≤ 368 :=
    (pow_le_pow_iff_left₀ hnn (by norm_num) (by norm_num)).mp hpow
  have hcount : (16 : ℝ) * (K : ℝ) ^ (19 : ℕ) ≤ (repCount (4168 * K ^ 27) : ℝ) := by
    have := repCount_ge_nineteen K
    exact_mod_cast this
  have hKpow : (0 : ℝ) ≤ (K : ℝ) ^ (19 : ℕ) := by positivity
  rw [hcast, hsplit]
  nlinarith [hconst, hcount, hKpow, hnn]
