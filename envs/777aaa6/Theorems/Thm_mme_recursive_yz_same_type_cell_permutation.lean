-- Prove2me | Theorems.Thm_mme_recursive_yz_same_type_cell_permutation
-- name    : mme_recursive_yz_same_type_cell_permutation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T11:06:28.46457+00:00
-- url     : https://prove2.me/theorems/6208a9f7-4a27-48f1-8458-144e9bc14b1a
-- title:
--   Equal recursive split types have the same physical cell partition up to permutation
-- statement:
--   Two recursive addresses with the same prescribed joint split counts have physical cell maps related by a permutation of child positions. The positions include both halves of each parent occurrence. For each cell $c$, its multiplicity is exactly $m(c)+m(\bar c)$, so a single position permutation identifies the cell partitions of any two target addresses. This is the normalization needed to treat the extracted tensors as damaged copies of one unbroken template.
-- source:
--   Finite recursive extraction in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 6.3--6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_x_hash_families
open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_recursive_yz_same_type_cell_permutation {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a b : Address half R parent n)
    (ha : a ∈ RecursiveXHash.target m) (hb : b ∈ RecursiveXHash.target m) :
    ∃ sigma : Equiv.Perm (Position n), ∀ p, fullCell htotal a (sigma p) = fullCell htotal b p  := by sorry
