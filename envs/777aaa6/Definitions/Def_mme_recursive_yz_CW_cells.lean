-- Prove2me | Definitions.Def_mme_recursive_yz_CW_cells
-- name    : mme_recursive_yz_CW_cells
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-12T10:54:51.283719+00:00
-- url     : https://prove2.me/theorems/b383ba7c-3fae-401f-b06a-8e9ae25e56ac
-- title:
--   Literal CW powers with graded exact profiles in physical cells
-- statement:
--   For a field $K$, CW parameter $q$, child level $\ell$, and $L$ child positions, the source is the literal tensor $\mathrm{CW}_q^{\otimes L2^{\ell-1}}$. Its canonical word basis records an actual CW coordinate in every elementary factor. The fine label at each child position is the word of actual CW coordinate grades.
--
--   Given a cell map, a grade triple per cell, and a fine-word histogram per cell and mode, the unbroken tensor is the simultaneous restriction to basis words with exactly those grades and histograms. Its coordinate indices and full fine-label blocks are defined explicitly. A permutation of child positions lifts to a permutation of all elementary factors. These are concrete tensor and label definitions for repairing the recursively extracted pieces.
-- source:
--   Finite cell-profile formulation of the common-position shuffles used in the Hole Lemma application of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.5; https://arxiv.org/html/2404.16349v2.

import Definitions.Def_mme_recursive_yz_cell_shuffles
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.DWZStep1Support Module
set_option autoImplicit false
universe u v w
namespace MME.RecursiveYZ.CWCells

abbrev WordIndex (q ell L : ℕ) := Fin (L * 2 ^ (ell - 1)) → ULift.{u} (Fin (q + 2))

noncomputable def source (K : Type u) [Field K] (q ell L : ℕ) : TensorObj K 3 :=
  (CWObj K q).kronPow (L * 2 ^ (ell - 1))

noncomputable def basis (K : Type u) [Field K] (q ell L : ℕ) (i : Fin 3) :
    Basis (WordIndex.{u} q ell L) K ((source K q ell L).V i) :=
  kronPowModeWordBasis (CWObj K q) i
    ((cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm) (L * 2 ^ (ell - 1))

/-- The literal fine grades in each CW child position. -/
def label {P : Type v} (q ell L : ℕ) (positions : Fin L ≃ P)
    (w : WordIndex.{u} q ell L) : P → CompleteWord ell :=
  fun p r ↦ cwSquareCoordGrade q (w (finProdFinEquiv (positions.symm p, r))).down

def grade {ell : ℕ} (w : CompleteWord ell) : ℕ := ∑ r, (w r).val

def allowed {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) (i : Fin 3) (x : WordIndex.{u} q ell L) : Prop :=
  (∀ p, grade (label q ell L positions x p) = shape (cell p) i) ∧
    Useful cell (mu i) (label q ell L positions x)

noncomputable def grading {P : Type v} {C : Type w} [Fintype P]
    (K : Type u) [Field K] (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) : (source K q ell L).TypeGrading 2 :=
  (source K q ell L).basisAllAllowedGrading (basis K q ell L)
    (allowed q ell L positions cell shape mu)

noncomputable def unbroken {P : Type v} {C : Type w} [Fintype P]
    (K : Type u) [Field K] (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) : TensorObj K 3 :=
  (source K q ell L).basisAllAllowedSubtensor (basis K q ell L)
    (allowed q ell L positions cell shape mu)

abbrev Coord {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) (i : Fin 3) :=
  {x : WordIndex.{u} q ell L // allowed q ell L positions cell shape mu i x}

abbrev Block {P : Type v} {C : Type w} [Fintype P]
    (ell : ℕ) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) (i : Fin 3) :=
  CellWord cell grade (fun c ↦ shape c i) (mu i)

/-- Lift a permutation of child positions to all of their elementary CW factors. -/
def leafPermutation {P : Type v} (ell L : ℕ) (positions : Fin L ≃ P) (e : Equiv.Perm P) :
    Equiv.Perm (Fin (L * 2 ^ (ell - 1))) :=
  (finProdFinEquiv.symm.trans
    (Equiv.prodCongr ((positions.trans e).trans positions.symm) (Equiv.refl _))).trans finProdFinEquiv

end MME.RecursiveYZ.CWCells


