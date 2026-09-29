-- Prove2me | Theorems.Thm_mme_profiled_CW_boundary_end_of_histogram_support
-- name    : mme_profiled_CW_boundary_end_of_histogram_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:53:12.144856+00:00
-- url     : https://prove2.me/theorems/807d33df-18f0-48bf-917e-cd4b24fd4f28
-- title:
--   Constructing boundary recipe leaves from exact histograms
-- statement:
--   Partition $L$ complete-word positions into cells at level $\ell$. In every cell, suppose the three grades sum to $2\cdot2^{\ell-1}$, at least one grade is zero, and each mode histogram has the cell multiplicity and is supported at its grade. Assume the complementary-word identities hold. Suppose the coordinate predicates defined by these grades and histograms lie inside a prescribed interface $P$ on $L2^{\ell-1}$ elementary CW positions.
--
--   Then these data determine exact oriented boundary profiles and a terminal boundary interface for $P$. The profiles reproduce every supplied grade and histogram. Each of the three matrix dimensions of the terminal interface is the product of the corresponding oriented profile dimensions. No tensor restriction is assumed.
-- source:
--   Exact complementary boundary profiles and the terminal ProfiledCW recipe interface.

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false

theorem mme_profiled_CW_boundary_end_of_histogram_support
    (ell L cells : ℕ) (cell : Fin L → Fin cells)
    (part : Partition cell) (shape : Fin cells → Fin 3 → ℕ)
    (mu : Fin 3 → Fin cells → CompleteWord ell → ℕ)
    (P : Predicate (L * 2 ^ (ell - 1)))
    (ht : ∀ j, shape (part.cells j) 0 + shape (part.cells j) 1 +
      shape (part.cells j) 2 = 2 * 2 ^ (ell - 1))
    (hm : ∀ j i, ∑ s, mu i (part.cells j) s = part.size j)
    (hg : ∀ j i s, 0 < mu i (part.cells j) s → grade s = shape (part.cells j) i)
    (hboundary : ∀ j,
      (shape (part.cells j) 2 = 0 → ∀ s,
        mu 1 (part.cells j) s = mu 0 (part.cells j) (fun r ↦ Fin.rev (s r))) ∧
      (shape (part.cells j) 0 = 0 → ∀ s,
        mu 2 (part.cells j) s = mu 1 (part.cells j) (fun r ↦ Fin.rev (s r))) ∧
      (shape (part.cells j) 1 = 0 → ∀ s,
        mu 2 (part.cells j) s = mu 0 (part.cells j) (fun r ↦ Fin.rev (s r))))
    (hz : ∀ j, ∃ z, shape (part.cells j) z = 0)
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
