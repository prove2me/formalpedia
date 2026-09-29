-- Prove2me | solution 1 for PadicBerggren.tree_parity_int
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:44.435567+00:00
-- url     : https://prove2.me/submissions/0f85bab9-ea52-4ea6-9424-9cd14279d290

-- Sol generated from Geometry/PadicBerggrenParity.lean
import Mathlib
import Definitions.Def_Geometry_PadicBerggrenDynamics

/-!
# The prime `2`: total collapse of the Berggren dynamics, and the parity of the tree

The p-adic analysis in `Catalog/Geometry/PadicBerggrenDynamics.lean` always excludes `p = 2`.
This file explains why, and turns the exclusion into a theorem: **mod `2` all three Berggren
generators are the identity matrix**, so the reduced dynamical system degenerates completely —
the infinite ternary tree maps to a single point.  The arithmetic shadow of this degeneracy is
the classical parity pattern of Pythagorean triples produced by the tree.

## Main results

* `PadicBerggren.B₁_mod_two`, `B₂_mod_two`, `B₃_mod_two`, `gen_mod_two` : each generator
  reduces to `1` in `ZMod 2`.
* `PadicBerggren.wordMat_mod_two` : hence every word in the generators reduces to `1`.
* `PadicBerggren.tree_mod_two` : every vertex of the Berggren tree is congruent to the root
  `(3,4,5) ≡ (1,0,1)` mod `2`; the mod-`2` dynamical system has exactly one orbit, a fixed
  point.  This is the "`if false`" scenario of the research programme, realised exactly at the
  prime `2`.
* `PadicBerggren.tree_parity_int` : the integral form — for every word `w`, the triple
  `wordMat ℤ w *ᵥ (3,4,5)` has odd first entry, even second entry and odd third entry.
  In particular no Berggren move can ever produce a triple with two odd legs.
* `PadicBerggren.tree_parity_not_all_odd` : consequently no vertex of the tree has both legs
  odd (an obstruction which, over `ZMod 2`, is exactly the statement that the null cone mod `2`
  is *not* all of `(ZMod 2)³`).
-/

open PadicBerggren

open Matrix










open PadicBerggren in
theorem solution(w : List (Fin 3)) :
    (wordMat ℤ w *ᵥ root ℤ) 0 % 2 = 1 ∧ (wordMat ℤ w *ᵥ root ℤ) 1 % 2 = 0 ∧
      (wordMat ℤ w *ᵥ root ℤ) 2 % 2 = 1 := by
  induction w with
  | nil =>
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [wordMat, Matrix.one_mulVec, root]
  | cons a w ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hstep : wordMat ℤ (a :: w) *ᵥ root ℤ = gen ℤ a *ᵥ (wordMat ℤ w *ᵥ root ℤ) := by
        simp [wordMat, List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]
      rw [hstep]
      set v : Fin 3 → ℤ := wordMat ℤ w *ᵥ root ℤ with hv
      fin_cases a <;>
        refine ⟨?_, ?_, ?_⟩ <;>
        simp [gen, B₁, B₂, B₃, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
        omega
