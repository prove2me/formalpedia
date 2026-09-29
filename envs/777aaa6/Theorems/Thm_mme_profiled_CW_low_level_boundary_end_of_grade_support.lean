-- Prove2me | Theorems.Thm_mme_profiled_CW_low_level_boundary_end_of_grade_support
-- name    : mme_profiled_CW_low_level_boundary_end_of_grade_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:53:21.70033+00:00
-- url     : https://prove2.me/theorems/8f9e9812-6dcd-44ab-a19a-95f8e9fe1b07
-- title:
--   Elementary-depth histograms automatically give boundary recipe leaves
-- statement:
--   Let $\ell\le1$ and partition $L$ complete-word positions into cells. Suppose each cell has three grades summing to $2\cdot2^{\ell-1}$ and three histograms, each with the cell multiplicity and supported at its specified grade. Assume the resulting coordinate predicates are contained in an interface $P$.
--
--   Then there are exact oriented boundary profiles reproducing those grades and histograms, together with a terminal boundary interface for $P$. Its three matrix dimensions are the products of the corresponding profile dimensions. No separate zero-mode or complementary-histogram hypothesis is needed: at this depth the grade total is two and a complete word is determined by its grade.
-- source:
--   Exact complementary boundary profiles and the terminal ProfiledCW recipe interface.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false

theorem mme_profiled_CW_low_level_boundary_end_of_grade_support
    (ell L cells : ℕ) (hlevel : ell ≤ 1) (cell : Fin L → Fin cells)
    (part : Partition cell) (shape : Fin cells → Fin 3 → ℕ)
    (mu : Fin 3 → Fin cells → CompleteWord ell → ℕ)
    (P : Predicate (L * 2 ^ (ell - 1)))
    (ht : ∀ j, shape (part.cells j) 0 + shape (part.cells j) 1 +
      shape (part.cells j) 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ j i, ∑ s, mu i (part.cells j) s = part.size j)
    (hg : ∀ j i s, 0 < mu i (part.cells j) s → grade s = shape (part.cells j) i)
    (hinside : ∀ i x,
      ((∀ p, grade (split (Equiv.refl (Fin L)) rfl x p) = shape (cell p) i) ∧
        Useful cell (mu i) (split (Equiv.refl (Fin L)) rfl x)) → P i x) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, shape (part.cells j) i = (profiles j).shape (z j) i) ∧
      (∀ j i, mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell (L * 2 ^ (ell - 1)) P,
        B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by sorry
