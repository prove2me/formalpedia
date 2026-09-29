-- Prove2me | solution 1 for HigherPythagorean.quad_two_parents_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:10:33.242633+00:00
-- url     : https://prove2.me/submissions/6438f9c3-27b3-4697-b203-5400ec289711

-- Sol generated from Shared/HigherPythagorean/BranchingContrast.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_content_dvd_fth
import Theorems.Thm_HigherPythagorean_content_dvd_thd
import Theorems.Thm_HigherPythagorean_content_eq_one_of_fst_one
import Theorems.Thm_HigherPythagorean_reach_of_prim

/-!
# Branching: why the Berggren tree is a tree in dimension 2 and **not** in dimension 3

A *descent* at a node is a sign pattern `ε ∈ {±1}ⁿ` for which the all-ones reflection move
strictly decreases the height.  Parents in a Berggren-type tree are exactly descents, so a node
has a unique parent iff it admits exactly one descent.

Main results.

* `triple_unique_descent` : a primitive Pythagorean triple with positive legs admits **exactly one**
  descent, namely `ε = (+,+)`.  This is the structural reason the Berggren graph is a *tree*.
* `quad_at_most_two_descents` : a Pythagorean quadruple admits at most **two** descents
  (`ε = (+,+,+)` and at most one pattern with a single minus sign).
* `quad_two_parents_family` : for every `m ≥ 2` the primitive quadruple `(1, 2m, 2m², 2m²+1)`
  really has two descents, landing on two *distinct* primitive quadruples of strictly smaller
  height, both of which are reachable from the root.  Hence the quadruple graph contains
  infinitely many nodes with two parents: it is **not** a tree.
* `triple_height_annulus`, `quad_height_annulus` : the exact integral form of the growth
  constants `3+2√2 = (1+√2)²` (triples, silver ratio) and `2+√3` (quadruples).
-/

open HigherPythagorean


/-! ## Triples: exactly one descent, hence a tree -/






/-! ## Quadruples: at most two descents -/







/-! ## Content shortcuts -/


theorem content_eq_one_of_consecutive (a b c : ℤ) : content a b c (c + 1) = 1 := by
  have h3 := content_dvd_thd a b c (c + 1)
  have h4 := content_dvd_fth a b c (c + 1)
  have hone : (content a b c (c + 1) : ℤ) ∣ 1 := by
    have := dvd_sub h4 h3
    simpa using this
  have : (content a b c (c + 1) : ℕ) ∣ 1 := by exact_mod_cast hone
  exact Nat.dvd_one.mp this

/-! ## An infinite family of quadruples with two parents -/

/-- The family `(1, 2m, 2m², 2m²+1)` consists of primitive Pythagorean quadruples. -/
theorem family_isPrimQuad (m : ℤ) : IsPrimQuad 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) := by
  refine ⟨by unfold IsPythQuadruple; ring, content_eq_one_of_fst_one _ _ _⟩

/-- First parent of `(1, 2m, 2m², 2m²+1)`: the all-plus descent, of height `2m²−2m+1`. -/
theorem family_parentA (m : ℤ) :
    IsPrimQuad (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) := by
  refine ⟨by unfold IsPythQuadruple; ring, content_eq_one_of_consecutive _ _ _⟩

/-- Second parent of `(1, 2m, 2m², 2m²+1)`: the one-minus descent, of height `2m²−2m+3`. -/
theorem family_parentB (m : ℤ) :
    IsPrimQuad (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) := by
  refine ⟨by unfold IsPythQuadruple; ring, ?_⟩
  have := content_eq_one_of_consecutive (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2)
  simpa [show 2 * m ^ 2 - 2 * m + 2 + 1 = 2 * m ^ 2 - 2 * m + 3 by ring] using this

/-- Both descents of the family node are genuine descents. -/
theorem family_two_descents (m : ℤ) (hm : 2 ≤ m) :
    Descends 1 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
      Descends (-1) 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) := by
  constructor <;> · unfold Descends; nlinarith





/-! ## Integral form of the growth constants -/




open HigherPythagorean in
theorem solution(m : ℤ) (hm : 2 ≤ m) :
    IsPrimQuad 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    Descends 1 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    Descends (-1) 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    IsPrimQuad (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
    IsPrimQuad (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
    Reach (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
    Reach (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
    (2 * m ^ 2 - 2 * m + 1 : ℤ) ≠ 2 * m ^ 2 - 2 * m + 3 := by
  obtain ⟨hd1, hd2⟩ := family_two_descents m hm
  obtain ⟨hA1, hA2⟩ := family_parentA m
  obtain ⟨hB1, hB2⟩ := family_parentB m
  refine ⟨family_isPrimQuad m, hd1, hd2, ⟨hA1, hA2⟩, ⟨hB1, hB2⟩, ?_, ?_, by omega⟩
  · exact reach_of_prim (2 * m ^ 2 - 2 * m + 1).toNat _ _ _ _ le_rfl (by linarith) le_rfl
      (by nlinarith) (by nlinarith) hA1 hA2
  · exact reach_of_prim (2 * m ^ 2 - 2 * m + 3).toNat _ _ _ _ le_rfl (by linarith) (by norm_num)
      (by nlinarith) (by nlinarith) hB1 hB2
