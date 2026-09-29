-- Prove2me | solution 1 for HigherPythagorean.boundary_move
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:55:58.993894+00:00
-- url     : https://prove2.me/submissions/a21c7354-781b-44c9-bde2-17b67fb3570f

-- Sol generated from Shared/HigherPythagorean/HyperbolicBoundary.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_HyperbolicBoundary
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The hyperbolic (ideal boundary) picture, and algebraicity of the growth constant

Normalising a null vector by its height embeds the Pythagorean quadruples into the ideal
boundary `S²` of the hyperbolic `4`-space (equivalently, the boundary sphere of the Poincaré
ball), and the reflection move acts there by an explicit affine–fractional (Möbius) formula.

* `sphere_of_quad` : a Pythagorean quadruple normalises to a rational point of the unit sphere.
* `boundary_move` : the reflection acts on the boundary by `u ↦ (u − s + 1)/(2 − s)`, where
  `s = (a+b+c)/d` is the *shadow* of the node; the height is multiplied by `2 − s`.
* `shadow_bound` : `|s| ≤ √3`, so the height multiplier `2 − s` lies in `[2−√3, 2+√3]`.
* `growth_const_quadratic` : the growth constant `(√n+1)/(√n−1)` of dimension `n` is an
  algebraic number of degree ≤ 2: it is a root of `(n−1)X² − 2(n+1)X + (n−1)`.  For `n = 2` this
  is `X²−6X+1` (root `3+2√2 = (1+√2)²`, silver ratio) and for `n = 3` it is `X²−4X+1`
  (root `2+√3`).
-/

open HigherPythagorean

/-! ## Boundary sphere -/





/-! ## Algebraicity of the growth constant -/





open HigherPythagorean in
theorem solution{a b c d : ℤ} (hd : 0 < d) (hs : (a + b + c : ℤ) ≠ 2 * d) :
    ((d - qk a b c d : ℤ) : ℚ) = (2 - shadow a b c d) * (d : ℚ) ∧
    (((a - qk a b c d : ℤ) : ℚ)) / ((d - qk a b c d : ℤ) : ℚ) =
      ((a : ℚ) / (d : ℚ) - shadow a b c d + 1) / (2 - shadow a b c d) := by
  have hd' : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hd)
  have hne : ((a : ℚ) + b + c) ≠ 2 * (d : ℚ) := by
    intro hcon
    apply hs
    have : ((a + b + c : ℤ) : ℚ) = ((2 * d : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h2s : (2 : ℚ) - shadow a b c d ≠ 0 := by
    unfold shadow
    intro hcon
    apply hne
    field_simp at hcon
    linarith
  have hnum : ((a - qk a b c d : ℤ) : ℚ) = (a : ℚ) - ((a : ℚ) + b + c) + (d : ℚ) := by
    unfold qk; push_cast; ring
  have hden : ((d - qk a b c d : ℤ) : ℚ) = 2 * (d : ℚ) - ((a : ℚ) + b + c) := by
    unfold qk; push_cast; ring
  have hdenne : (2 * (d : ℚ) - ((a : ℚ) + b + c)) ≠ 0 := by
    intro hcon; exact hne (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hden]
    unfold shadow
    field_simp
  · rw [hnum, hden]
    unfold shadow at h2s ⊢
    rw [div_eq_div_iff hdenne h2s]
    field_simp
