-- Prove2me | solution 1 for HigherPythagorean.quad_one_descent_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:06:42.836995+00:00
-- url     : https://prove2.me/submissions/8619ac6c-2a90-4eb1-904e-366c40bd1a08

-- Sol generated from Shared/HigherPythagorean/HarmonicLaw.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_descend_at_most_one_minus

/-!
# The harmonic branching law for Pythagorean quadruples

`BranchingContrast` shows that a Pythagorean quadruple has at most two parents.  Here we
determine *exactly when* the second parent exists, and the answer is an Egyptian-fraction
("harmonic") law:

> the reflection move with a minus sign on the coordinate `a` descends **iff** `1/a > 1/b + 1/c`.

This is the dimension-three replacement for the (empty) second-parent condition of the Berggren
tree, and it explains all the phenomena observed in dimension three:

* `quad_minus_descent_iff` / `quad_minus_descent_iff_rat` : the law, in integral and harmonic form.
* `harmonic_law_at_most_one_index` : the harmonic inequality can hold for at most one coordinate
  (a two-line proof of the "at most two parents" bound).
* `quad_neutral_move_iff` : the boundary case `1/a = 1/b + 1/c` gives a *height preserving*
  ("horizontal") move — a phenomenon that does not exist for triples (`triple_no_neutral_move`),
  realised e.g. by the quadruple `(1,2,2,3)`.
* `quad_one_descent_family` : the family `(2m, 2m, 2m²−1, 2m²+1)` has a **unique** parent, while
  `(1, 2m, 2m², 2m²+1)` has two; hence (`quad_branching_not_constant`) the branching number of
  the quadruple graph is genuinely non-constant, taking both possible values infinitely often.
-/

open HigherPythagorean

/-! ## The harmonic law -/

/-- **Harmonic branching law (integral form).**  The move with a minus sign on the first
coordinate strictly decreases the height iff `a(b+c) < bc`. -/
theorem quad_minus_descent_iff {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : IsPythQuadruple a b c d) : Descends (-1) 1 1 a b c d ↔ a * (b + c) < b * c := by
  unfold IsPythQuadruple at h
  unfold Descends
  constructor
  · intro hdes
    nlinarith
  · intro hlaw
    have hbc : a < b + c := by nlinarith
    nlinarith



/-! ## Neutral (height preserving) moves -/




/-! ## A family with a unique parent -/

lemma descends_swap12 (a b c d : ℤ) : Descends 1 (-1) 1 a b c d ↔ Descends (-1) 1 1 b a c d := by
  unfold Descends; constructor <;> intro h <;> linarith

lemma descends_swap13 (a b c d : ℤ) : Descends 1 1 (-1) a b c d ↔ Descends (-1) 1 1 c b a d := by
  unfold Descends; constructor <;> intro h <;> linarith





open HigherPythagorean in
theorem solution(m : ℤ) (hm : 2 ≤ m) :
    ∃! p : ℤ × ℤ × ℤ, (IsSign p.1 ∧ IsSign p.2.1 ∧ IsSign p.2.2) ∧
      Descends p.1 p.2.1 p.2.2 (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
  have hpos1 : (0 : ℤ) < 2 * m := by linarith
  have hpos3 : (0 : ℤ) < 2 * m ^ 2 - 1 := by nlinarith
  have hposd : (0 : ℤ) < 2 * m ^ 2 + 1 := by nlinarith
  have hq : IsPythQuadruple (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
    unfold IsPythQuadruple; ring
  have hq12 : IsPythQuadruple (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := hq
  have hq13 : IsPythQuadruple (2 * m ^ 2 - 1) (2 * m) (2 * m) (2 * m ^ 2 + 1) := by
    unfold IsPythQuadruple; ring
  refine ⟨(1, 1, 1), ⟨⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩, by unfold Descends; nlinarith⟩, ?_⟩
  rintro ⟨e₁, e₂, e₃⟩ ⟨⟨hs1, hs2, hs3⟩, hdes⟩
  -- no coordinate satisfies the harmonic inequality
  have hno1 : ¬ Descends (-1) 1 1 (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
    rw [quad_minus_descent_iff hpos1 hpos1 hpos3 hposd hq]
    push_neg
    nlinarith
  have hno2 : ¬ Descends 1 (-1) 1 (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
    rw [descends_swap12, quad_minus_descent_iff hpos1 hpos1 hpos3 hposd hq12]
    push_neg
    nlinarith
  have hno3 : ¬ Descends 1 1 (-1) (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by
    rw [descends_swap13, quad_minus_descent_iff hpos3 hpos1 hpos1 hposd hq13]
    push_neg
    nlinarith
  have hcoord := descend_at_most_one_minus (le_of_lt hpos1) (le_of_lt hpos1) (le_of_lt hpos3)
    hposd hq hs1 hs2 hs3 hdes
  rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl <;> rcases hs3 with rfl | rfl
  · rfl
  · exact absurd hdes hno3
  · exact absurd hdes hno2
  · simp at hcoord
  · exact absurd hdes hno1
  · simp at hcoord
  · simp at hcoord
  · simp at hcoord
