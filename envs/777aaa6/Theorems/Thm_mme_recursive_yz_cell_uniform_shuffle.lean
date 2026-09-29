-- Prove2me | Theorems.Thm_mme_recursive_yz_cell_uniform_shuffle
-- name    : mme_recursive_yz_cell_uniform_shuffle
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-12T10:55:24.289723+00:00
-- url     : https://prove2.me/theorems/1783bd7d-a01a-4fd6-9e79-48a7c327e19a
-- title:
--   Uniform cell-preserving shuffles of graded exact-profile blocks
-- statement:
--   Let $P$ be a finite position set partitioned into cells, and prescribe the grade and full fine-word histogram in each cell. The group of position permutations preserving every cell acts on the resulting graded exact-profile blocks by precomposition with the inverse permutation. There exists a uniform available-block shuffle system for this concrete action.
--
--   Thus a uniformly chosen common position shuffle sends each block uniformly over the complete block set. The same shuffle group is available simultaneously in all three tensor modes, as required by finite hole repair.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Claim 6.21 and the simultaneous filtering/Hole Lemma step in Section 6.5; https://arxiv.org/html/2404.16349v2#S6.SS5. Explicit finite constants are a conservative formalization of the source argument.

import Definitions.Def_mme_recursive_yz_cell_shuffles
import Definitions.Def_mme_dwz_hole_cover_data
open BigOperators MME.RecursiveYZ MME.DWZSquare
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_yz_cell_uniform_shuffle {P C W D : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ) :
    ∃ system : AvailableBlockShuffle (CellWord cell grade shape mu) (cellPerm cell),
      ∀ e source, (system.move e source).val = fun p ↦ source.val (e.val.symm p)  := by sorry
