-- Prove2me | Definitions.Def_mme_dwz_source_aligned_broken_obj
-- name    : mme_dwz_source_aligned_broken_obj
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T13:43:46.28425+00:00
-- url     : https://prove2.me/theorems/19a66053-04e1-4667-ac64-177203af61f0
-- title:
--   A literal DWZ broken copy in retained source-position order
-- statement:
--   Fix a retained Table-2 outer component word $I$ and a broken-copy mask on its useful fine $Z$ blocks. The coarse source address block is the ordered product, in the original positions of $I$, of the corresponding canonical five-graded blocks of $CW_6^{\otimes 2}$. Its $Z$ mode has the canonical heterogeneous product basis. A basis word records one fine pair of CW grades at every position.
--
--   A word survives exactly when its componentwise split histograms have the prescribed Table-2 counts and the resulting literal useful block belongs to the supplied nonhole set. The source-aligned broken object is the single $Z$-basis projection retaining precisely these words:
--
--   $$
--   B_I^{\mathrm{src}}=\operatorname{Proj}_{Z,\,\mathrm{nonholes}}(T_I).
--   $$
--
--   The complete $X$ and $Y$ spaces of the coarse address remain shared inside this one tensor. In particular, the construction is not a direct sum over useful fine blocks and does not clone shared variables. Keeping the original source-position order makes the mixed-term vanishing obligation from Additional Zeroing-Out Step 2 explicit before any Table-2 regrouping.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 and Additional Zeroing-Out Step 2 in Section 6, printed pp. 46--55; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_broken_standard_obj
import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_induced_word_zeroing

open MME Module

universe u

namespace MME.DWZSourceAligned

set_option autoImplicit false
set_option warningAsError true

/-- The literal coarse five-grading address attached to a Table-2 outer
component word. -/
def coarseAddress {N : ℕ} (outer : Fin N → Fin 15) :
    Fin 3 → Fin N → Fin 5 :=
  fun i r ↦ cwSquareBlockType
    (DWZSquare.shapeX (outer r))
    (DWZSquare.shapeY (outer r))
    (DWZSquare.shapeZ (outer r)) i

/-- The source-aligned coarse address block, before the small-Z nonhole
projection.  Its positions remain in the original retained-word order. -/
noncomputable def coarseAddressObj
    (K : Type u) [Field K] {N : ℕ} (outer : Fin N → Fin 15) :
    TensorObj K 3 :=
  gradedAddressBlock (cwSquareCanonicalGrading K 6) (coarseAddress outer)

/-- Canonical Z-basis words of one source-aligned coarse address block. -/
abbrev AddressZWord {N : ℕ} (outer : Fin N → Fin 15) : Type u :=
  ∀ r : Fin N,
    DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (DWZSquare.shapeZ (outer r))

/-- The actual heterogeneous product basis of the Z mode of a retained
coarse address block. -/
noncomputable def coarseAddressZBasis
    (K : Type u) [Field K] {N : ℕ} (outer : Fin N → Fin 15) :
    Basis (AddressZWord outer) K ((coarseAddressObj K outer).V 2) := by
  unfold coarseAddressObj gradedAddressBlock coarseAddress
  exact TensorObj.kronFinModePiBasis N
    (fun r ↦ DWZComponentRestriction.canonicalComponentBlock K (outer r)) 2
    (fun r ↦
      DWZComponentRestriction.canonicalComponentZBasis K (outer r))

/-- Read the two fine CW grades from a canonical source-aligned Z-basis
word. -/
def addressFineZ {N : ℕ} {outer : Fin N → Fin 15}
    (W : AddressZWord outer) : Fin N → Fin 3 × Fin 3 :=
  fun r ↦ ((W r).leftGrade, (W r).rightGrade)

/-- The exact Definition-6.3 componentwise split histogram for a Z-basis
word in the original retained-word order. -/
def addressWordUseful (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (W : AddressZWord outer) : Prop :=
  ∀ (s : Fin 15) (a : Fin 3),
    Fintype.card
        {r : Fin N // outer r = s ∧ (W r).leftGrade = a} =
      DWZTable2Counts.split s a * m

/-- A useful source-aligned Z-basis word gives the literal `UsefulBlock`
label used by Claim 6.8 and the hole mask. -/
def addressUsefulBlock
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (W : AddressZWord outer) (hW : addressWordUseful m outer W) :
    DWZTable2StandardForm.UsefulBlock m outer :=
  ⟨addressFineZ W,
    fun r ↦ by
      apply Fin.ext
      exact congrArg Fin.val (W r).down.2,
    hW⟩

/-- A canonical source Z-basis word survives exactly when it is useful and
its literal useful-block label is a nonhole of the supplied broken copy. -/
def addressWordSurvives
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer))
    (W : AddressZWord outer) : Prop :=
  ∃ hW : addressWordUseful m outer W,
    addressUsefulBlock m outer W hW ∈ copy.nonholes

/-- The source-aligned broken-copy grading.  It leaves the complete X/Y
spaces of one coarse retained address and projects only the Z basis onto
literal useful nonholes. -/
noncomputable def brokenAddressGrading
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) :
    (coarseAddressObj K outer).TypeGrading 2 := by
  letI : DecidablePred (addressWordSurvives m outer copy) :=
    Classical.decPred _
  exact (coarseAddressObj K outer).basisZAllowedGrading
    (coarseAddressZBasis K outer) (addressWordSurvives m outer copy)

/-- One literal broken Table-2 copy in source position order.  Unlike a
`bigAdd` of useful blocks, this object keeps their shared X/Y mode spaces. -/
noncomputable def brokenAddressObj
    (K : Type u) [Field K]
    (m : ℕ) {N : ℕ} (outer : Fin N → Fin 15)
    (copy : DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m outer)) : TensorObj K 3 :=
  (brokenAddressGrading K m outer copy).blockSubtensor (fun _ ↦ 0)

end MME.DWZSourceAligned


