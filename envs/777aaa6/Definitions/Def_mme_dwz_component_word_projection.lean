-- Prove2me | Definitions.Def_mme_dwz_component_word_projection
-- name    : mme_dwz_component_word_projection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:06:10.985495+00:00
-- url     : https://prove2.me/theorems/962cd2bf-b0ef-4842-a3a6-ae16975fd85f
-- title:
--   Canonical available-word projection of a Table-2 component power
-- statement:
--   For each of the fifteen Table-2 components at $q=6$ and each scale $m\geq0$, form the literal canonical five-graded component block and raise it to the prescribed power $n_s m$. Its $Z$ mode has a canonical word basis: each letter is a canonical coordinate pair of coarse grade $k_s$, and each word has length $n_s m$.
--
--   A word is declared available exactly when, for every left split grade $a\in\{0,1,2\}$,
--
--   $$
--   \#\{r:\text{the left grade at position }r\text{ is }a\}=n_{s,a}m,
--   $$
--
--   where $n_{s,a}$ is the exact integer Table-2 split count. The associated two-class grading leaves the complete $X$ and $Y$ spaces in the selected class and splits only this $Z$ word basis into available and unavailable words. Its all-selected block is the restricted component power.
--
--   This is the literal component factor $T_s^{\otimes n_sm}[\widetilde\alpha_s]$ needed by the DWZ standard-form tensor; it is one $Z$ projection and not a direct sum that clones the shared $X$ or $Y$ variables.
--
--   **Formalization Note** Canonical coordinate-pair indices are universe-lifted only to match the field/module universe; basis reindexing leaves every represented vector unchanged. The construction includes $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Definitions 5.2--5.4, PDF pp. 47--48 / printed pp. 46--47, specialized to the q=6 parameters in Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_pair_coarsening
import Definitions.Def_mme_CW_square_canonical_grading
import Mathlib.LinearAlgebra.Basis.Submodule

open MME Module TensorProduct

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

variable {K : Type u} [Field K]

/-- Coordinate pairs in the canonical square basis carrying one fixed coarse
grade. -/
def CoarsePair (q : ℕ) (c : Fin 5) :=
  {p : Fin (q + 2) × Fin (q + 2) // cwSquarePairGrade q p = c}

instance coarsePairFintype (q : ℕ) (c : Fin 5) : Fintype (CoarsePair q c) :=
  by
    unfold CoarsePair
    infer_instance

instance coarsePairDecidableEq (q : ℕ) (c : Fin 5) :
    DecidableEq (CoarsePair q c) := by
  unfold CoarsePair
  infer_instance

/-- The canonical subset basis of one coarse square-grading class. -/
noncomputable def coarseClassBasis
    (q : ℕ) (i : Fin 3) (c : Fin 5) :
    Basis (CoarsePair q c) K
      ((cwSquareCanonicalGrading K q).classOf i c) := by
  let b := cwSquareCanonicalBasis K q i
  let v : CoarsePair q c →
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V i) := fun p => b p.1
  have hv : LinearIndependent K v := by
    simpa [v, Function.comp_def] using
      b.linearIndependent.comp (fun p : CoarsePair q c ↦ p.1)
        Subtype.val_injective
  have hset : Set.range v =
      b '' {p | cwSquarePairGrade q p = c} := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  change Basis (CoarsePair q c) K
    (cwBasisGrade (cwSquareCanonicalBasis K q i)
      (cwSquarePairGrade q) c)
  unfold cwBasisGrade
  rw [← hset]
  exact Basis.span hv

/-- The left fine split grade carried by one canonical coarse-class basis
index. -/
def CoarsePair.leftGrade {q : ℕ} {c : Fin 5} (p : CoarsePair q c) : Fin 3 :=
  cwSquareCoordGrade q p.1.1

/-- The right fine split grade carried by one canonical coarse-class basis
index. -/
def CoarsePair.rightGrade {q : ℕ} {c : Fin 5} (p : CoarsePair q c) : Fin 3 :=
  cwSquareCoordGrade q p.1.2

/-- Universe-lifted canonical pair indices.  The lift changes only the index
type's universe and not the represented basis vectors. -/
def LiftedCoarsePair (q : ℕ) (c : Fin 5) : Type u :=
  ULift.{u} (CoarsePair q c)

instance liftedCoarsePairFintype (q : ℕ) (c : Fin 5) :
    Fintype (LiftedCoarsePair.{u} q c) := by
  unfold LiftedCoarsePair
  infer_instance

instance liftedCoarsePairDecidableEq (q : ℕ) (c : Fin 5) :
    DecidableEq (LiftedCoarsePair.{u} q c) := by
  unfold LiftedCoarsePair
  infer_instance

def LiftedCoarsePair.leftGrade {q : ℕ} {c : Fin 5}
    (p : LiftedCoarsePair.{u} q c) : Fin 3 :=
  p.down.leftGrade

def LiftedCoarsePair.rightGrade {q : ℕ} {c : Fin 5}
    (p : LiftedCoarsePair.{u} q c) : Fin 3 :=
  p.down.rightGrade

/-- The literal canonical five-graded component block in Table-2 row `s`, at
the paper's parameter `q = 6`. -/
noncomputable def canonicalComponentBlock (K : Type u) [Field K]
    (s : Fin 15) : TensorObj K 3 :=
  (cwSquareCanonicalGrading K 6).blockSubtensor
    (cwSquareBlockType
      (MME.DWZSquare.shapeX s)
      (MME.DWZSquare.shapeY s)
      (MME.DWZSquare.shapeZ s))

/-- The canonical basis of the Z mode of one literal Table-2 component. -/
noncomputable def canonicalComponentZBasis (K : Type u) [Field K]
    (s : Fin 15) :
    Basis (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s)) K
      ((canonicalComponentBlock K s).V 2) :=
  (coarseClassBasis (K := K) 6 2
    (MME.DWZSquare.shapeZ s)).reindex Equiv.ulift.symm

/-- The recursive canonical Z-word basis of the prescribed component power. -/
noncomputable def componentPowerZBasis (K : Type u) [Field K]
    (s : Fin 15) (m : ℕ) :
    Basis
      (PowIndex (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s))
        (MME.DWZTable2Counts.component s * m)) K
      (((canonicalComponentBlock K s).kronPow
        (MME.DWZTable2Counts.component s * m)).V 2) :=
  kronPowModeBasis (canonicalComponentBlock K s) 2
    (canonicalComponentZBasis K s)
    (MME.DWZTable2Counts.component s * m)

/-- Definition-5.4 availability for a Z word in one fixed Table-2 component:
the number of positions with each left split grade is exactly the component's
integer split count times `m`. -/
def componentWordAllowed (s : Fin 15) (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6
      (MME.DWZSquare.shapeZ s))
      (MME.DWZTable2Counts.component s * m)) : Prop :=
  ∀ a : Fin 3,
    Fintype.card
        {r : Fin (MME.DWZTable2Counts.component s * m) //
          (PowIndex.get _ w r).leftGrade = a} =
      MME.DWZTable2Counts.split s a * m

/-- The two-class grading of a Table-2 component power that leaves X and Y
whole and separates exactly the available Z words. -/
noncomputable def componentPowerProjectionGrading
    (K : Type u) [Field K] (s : Fin 15) (m : ℕ) :
    ((canonicalComponentBlock K s).kronPow
      (MME.DWZTable2Counts.component s * m)).TypeGrading 2 := by
  letI : DecidablePred (componentWordAllowed s m) := Classical.decPred _
  exact
    ((canonicalComponentBlock K s).kronPow
      (MME.DWZTable2Counts.component s * m)).basisZAllowedGrading
        (componentPowerZBasis K s m) (componentWordAllowed s m)

/-- The source-faithful Table-2 restricted component power.  It is one
Z-only allowed-word projection of the literal canonical component power. -/
noncomputable def restrictedComponentPower (K : Type u) [Field K]
    (s : Fin 15) (m : ℕ) : TensorObj K 3 :=
  (componentPowerProjectionGrading K s m).blockSubtensor (fun _ ↦ 0)

end MME.DWZComponentRestriction


