-- Prove2me | Theorems.Thm_BookSixth_patch_agrees_with_its_own_similarity
-- name    : BookSixth.patch_agrees_with_its_own_similarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T20:38:56.412293+00:00
-- url     : https://prove2.me/theorems/ac9094b3-ea63-4895-8a85-0814b5dd0cb4
-- title:
--   The cut-off patched displacement agrees exactly with the i-th similarity on a point where the i-th cut-off is one and all the others vanish
-- statement:
--   The algebraic core of the cut-off patching construction. Given finitely many scalar cut-offs chi_j and maps S_j on R^3, form the patched displacement x |-> sum_j chi_j(x) * (S_j(x) - x). At a point x where the i-th cut-off equals exactly 1 and every other cut-off vanishes, the patch collapses to the i-th map S_i, with no hypothesis whatsoever on the other maps S_j and no hypothesis on how quickly the cut-offs vary.
--
--   This is exactly the locality that makes the roundness argument work. The ambient map produced by patching is anisotropic away from the components, but on any point where the cut-offs separate - the i-th is one and the rest are zero - it agrees EXACTLY with the prescribed similarity S_i. Anisotropy elsewhere therefore does not damage the image of that component, and the image of the component remains a round circle.
--
--   The statement is deliberately a purely algebraic identity with no topological content, so it is short, certain, and reusable by any later construction that patches ambient maps.
-- source:
--   Chapter 15 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The identity is Finset.sum_eq_single on the finite sum, together with the additive group laws of Space3 = Fin 3 -> R. It is the hinge between the cut-off patching construction and BookSixth.localized_similarity_isotopy_keeps_roundness (f90b81d4-2047-4b46-b7f7-15dc7f938dac, Proved), which converts agreement on a component into RoundCircle.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.patch_agrees_with_its_own_similarity {n : ℕ} (i : Fin n)
    (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3) (x : Space3)
    (hone : chi i x = 1) (hzero : ∀ j ∈ Finset.univ, j ≠ i → chi j x = 0) :
    x + ∑ j, chi j x • (S j x - x) = S i x := by sorry
