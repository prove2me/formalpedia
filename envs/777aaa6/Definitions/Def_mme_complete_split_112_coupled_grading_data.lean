-- Prove2me | Definitions.Def_mme_complete_split_112_coupled_grading_data
-- name    : mme_complete_split_112_coupled_grading_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-06T22:12:36.979234+00:00
-- url     : https://prove2.me/theorems/4d315fba-53f8-470e-acd7-8e5870e63fbb
-- title:
--   Concrete general-q coupled coordinate grading for complete profiles
-- statement:
--   Let K be any field and q a nonnegative integer. On the existing coupled112 coordinate sets, give the left and right X/Y families grades0 and1, the two distinguished Z coordinates grades0 and1, and the q-by-q Z family grade2. Use the actual standard coordinate basis in each mode and partition its span by those grades. This defines a specific three-grading of the existing coupled tensor, not an existentially chosen grading. Universe-lifted coordinates, grades and reindexed bases provide the same data for the existing tensor-power and complete-profile projection interfaces. No support theorem, matrix-multiplication block identification, profile feasibility, or value estimate is assumed by the definition.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9 (1990), coupled constituent on journal pp266 and270. Concrete coordinate-grading implementation reused from research/agents/cw_coupled_core/CoupledThreeGradingSolution.lean, now on existing public DWZCanonical112Coord. Complete-profile consumer: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4-3.6 and Proposition6.3/Theorem6.4.

import Definitions.Def_mme_dwz_q6_canonical_112_router_data
import Definitions.Def_mme_complete_split_112_address_words

set_option autoImplicit false
set_option warningAsError true

open Module

universe u

namespace MME.CompleteSplit112

/-- Internal coupled grades on the existing public canonical112 coordinate
type: X/Y left and right families are 0 and 1; the Z low coordinates are 0
and 1, and its q-by-q family is 2. -/
def coordGrade (q : ℕ) : ∀ s : Fin 3, DWZCanonical112Coord q s → Fin 3
  | ⟨0, _⟩, Sum.inl _ => 0
  | ⟨0, _⟩, Sum.inr _ => 1
  | ⟨1, _⟩, Sum.inl _ => 0
  | ⟨1, _⟩, Sum.inr _ => 1
  | ⟨2, _⟩, Sum.inl a => ⟨a.val, by omega⟩
  | ⟨2, _⟩, Sum.inr _ => 2

instance coordFintype (q : ℕ) (s : Fin 3) :
    Fintype (DWZCanonical112Coord q s) :=
  match s with
  | ⟨0, _⟩ => inferInstanceAs (Fintype (Fin q ⊕ Fin q))
  | ⟨1, _⟩ => inferInstanceAs (Fintype (Fin q ⊕ Fin q))
  | ⟨2, _⟩ => inferInstanceAs (Fintype (Fin 2 ⊕ (Fin q × Fin q)))

instance coordDecidableEq (q : ℕ) (s : Fin 3) :
    DecidableEq (DWZCanonical112Coord q s) :=
  match s with
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq (Fin q ⊕ Fin q))
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (Fin q ⊕ Fin q))
  | ⟨2, _⟩ => inferInstanceAs (DecidableEq (Fin 2 ⊕ (Fin q × Fin q)))

/-- The actual standard coordinate basis of the explicit coupled tensor,
using the existing public coordinate type, not a replacement type. -/
noncomputable def coordBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (DWZCanonical112Coord q s) K ((coupledObj K q).V s) :=
  match s with
  | ⟨0, _⟩ => Pi.basisFun K (Fin q ⊕ Fin q)
  | ⟨1, _⟩ => Pi.basisFun K (Fin q ⊕ Fin q)
  | ⟨2, _⟩ => Pi.basisFun K (Fin 2 ⊕ (Fin q × Fin q))

/-- Concrete three-grading of the coupled tensor by its actual standard
coordinate families. Its support and MM block identifications are separate
theorem obligations, not fields assumed by this definition. -/
noncomputable def grading
    (K : Type u) [Field K] (q : ℕ) : (coupledObj K q).TypeGrading 3 where
  decomp s := cwBasisGrade (coordBasis K q s) (coordGrade q s)
  is_internal s := cwBasisGrade_isInternal (coordBasis K q s) (coordGrade q s)

/-- Universe lift needed by the existing tensor-power basis and complete
profile projection APIs; the underlying coupled coordinate is unchanged. -/
abbrev LiftedCoord (q : ℕ) (s : Fin 3) : Type u :=
  ULift.{u} (DWZCanonical112Coord q s)

def liftedCoordGrade (q : ℕ) (s : Fin 3) (c : LiftedCoord.{u} q s) : Fin 3 :=
  coordGrade q s c.down

noncomputable def liftedCoordBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (LiftedCoord.{u} q s) K ((coupledObj K q).V s) :=
  (coordBasis K q s).reindex Equiv.ulift.symm

end MME.CompleteSplit112


