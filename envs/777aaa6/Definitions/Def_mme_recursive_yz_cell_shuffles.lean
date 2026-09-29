-- Prove2me | Definitions.Def_mme_recursive_yz_cell_shuffles
-- name    : mme_recursive_yz_cell_shuffles
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:40:33.706216+00:00
-- url     : https://prove2.me/theorems/4a208341-0901-47ac-9ce8-42c3452725d1
-- title:
--   Cell-preserving permutations and graded exact-profile blocks
-- statement:
--   A cell-preserving shuffle is a permutation of the physical child positions that preserves their full coarse-cell label. The resulting permutations form a finite group whenever the position set is finite.
--
--   A graded exact-profile block assigns a full fine word to every child position, with the prescribed grade of that cell and with a prescribed histogram inside every cell. These blocks are the fine-label universe of an unbroken cell-profile tensor. Applying one cell-preserving shuffle simultaneously to all modes is the concrete symmetry used in finite hole repair.
-- source:
--   Finite cell-profile formulation of the common-position shuffles used in the Hole Lemma application of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_compatibility
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
namespace MME.RecursiveYZ

/-- Common permutations of physical child positions preserving their full coarse cell. -/
def cellPerm {P C : Type*} (cell : P → C) : Subgroup (Equiv.Perm P) where
  carrier := {e | ∀ p, cell (e p) = cell p}
  one_mem' := fun _ ↦ rfl
  mul_mem' := by
    intro a b ha hb p
    exact (ha (b p)).trans (hb p)
  inv_mem' := by
    intro a ha p
    simpa only [Equiv.apply_symm_apply] using (ha (a.symm p)).symm

/-- Full fine-word blocks of an unbroken cell-profile tensor, including actual grades. -/
abbrev CellWord {P C W D : Type*} [Fintype P]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ) :=
  {f : P → W // (∀ p, grade (f p) = shape (cell p)) ∧ Useful cell mu f}

end MME.RecursiveYZ


