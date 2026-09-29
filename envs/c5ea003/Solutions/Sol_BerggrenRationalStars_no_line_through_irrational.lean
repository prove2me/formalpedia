-- Prove2me | solution 1 for BerggrenRationalStars.no_line_through_irrational
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:46:53.018526+00:00
-- url     : https://prove2.me/submissions/69e83ebb-3a71-42a1-b8b9-8cbd92107060

-- Sol generated from Cryptography/BerggrenStars/StarHierarchy.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars
import Theorems.Thm_BerggrenHypercycleStars_hpoint_im
import Theorems.Thm_BerggrenHypercycleStars_hpoint_re

/-!
# Why the stars sit at rationals, and why only finitely many of them are visible

Two complementary facts finish the explanation of the star map of the Berggren tree.

## Main results

* `no_line_through_irrational` : **there is no star at an irrational boundary point.** If two
  Berggren nodes lie on one Euclidean line through an ideal point `α` with `α` irrational, then
  they are the same node. Radial lines can only emanate from *rational* boundary points; the
  irrational directions of the picture carry no line at all, however dense the nodes are near
  them.
* `finite_visible_stars` : **the visible hierarchy is finite.** For every resolution threshold
  `ε > 0` only finitely many rationals `p/q ∈ [0,1]` have a star of resolution
  `δ(p/q) = starGapNum p q / q ≥ ε`. Combined with `BerggrenRationalStars.visible_rationals`,
  which computes the list for `ε = 2/5`, this says the star map has a discrete, computable
  hierarchy of visible directions rather than a continuum of them.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars




open BerggrenRationalStars in
theorem solution(a : ℝ) (ha : Irrational a) (m n m' n' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (c : ℝ)
    (h1 : (hpoint m n hm).re = a + c * (hpoint m n hm).im)
    (h2 : (hpoint m' n' hm').re = a + c * (hpoint m' n' hm').im) :
    m = m' ∧ n = n' := by
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM' : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast hm'
  rw [hpoint_re, hpoint_im] at h1 h2
  have e1 : (n : ℝ) = a * m + c := by
    field_simp at h1
    linarith
  have e2 : (n' : ℝ) = a * m' + c := by
    field_simp at h2
    linarith
  have key : a * ((m : ℝ) - m') = (n : ℝ) - n' := by linarith
  have hmm : m = m' := by
    by_contra hne
    have hd : ((m : ℝ) - m') ≠ 0 := by
      intro h0
      exact hne (by exact_mod_cast sub_eq_zero.mp h0)
    have hval : a = ((n : ℝ) - n') / ((m : ℝ) - m') := by
      rw [eq_div_iff hd]
      linarith
    refine ha ⟨(((n : ℤ) - (n' : ℤ)) : ℚ) / (((m : ℤ) - (m' : ℤ)) : ℚ), ?_⟩
    push_cast
    exact hval.symm
  subst hmm
  refine ⟨rfl, ?_⟩
  have : (n : ℝ) = (n' : ℝ) := by linarith
  exact_mod_cast this
