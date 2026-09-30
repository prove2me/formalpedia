-- Prove2me | Theorems.Thm_Hirsch_hpoly_and_row_faces_diamLE_two_of_normal_relations
-- name    : Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T15:56:46.059272+00:00
-- url     : https://prove2.me/theorems/96cb14a4-aa1b-4d14-93d9-b959e08aa662
-- title:
--   Positive normal-relation certificates give intrinsic diameter two
-- statement:
--   Consider an n-row real H-polyhedron in R^d, with n=d+2 and a reference extreme vertex. Suppose c_i>0, the slopes t_i are not all equal, sum_i c_i a_i=0, sum_i t_i c_i a_i=0, and sum_i c_i b_i=1. Then the H-polyhedron has padded vertex-edge diameter at most two. Moreover every face obtained by requiring any chosen collection of the original inequalities to be tight has intrinsic padded graph diameter at most two. All hypotheses are finite normal-relation certificates; no diameter bound is assumed. Existence of such certificates from boundedness alone is not asserted.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/4a9204edd7f03c7f9676f9dc9762be121e43bf1a ; standalone Lean/Axiom gate Actions run 34615241828

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem hpoly_and_row_faces_diamLE_two_of_normal_relations
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (ht : ∃ i j, t i ≠ t j)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0)
    (hmass : (∑ i, c i * b i) = 1)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (Hpoly a b) 2 ∧
      ∀ S : Finset (Fin n),
        DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by sorry
end Hirsch
