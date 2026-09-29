-- Prove2me | Definitions.Def_mme_dwz_fourth_child_coordinate_join_data
-- name    : mme_dwz_fourth_child_coordinate_join_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T08:45:24.958762+00:00
-- url     : https://prove2.me/theorems/bad3c47b-0006-4185-8c84-1db5e399345b
-- title:
--   Canonical joining of two CW-square coordinates inside a fourth-power coarse class
-- statement:
--   For the canonical fourth power $(\mathrm{CW}_q\otimes\mathrm{CW}_q)\otimes(\mathrm{CW}_q\otimes\mathrm{CW}_q)$, this module records its coarse $Z$-coordinate fiber of grade $L$, the left-square grade map, and the operation that joins coordinates from square coarse classes $k$ and $\ell$ whenever $k+\ell=L$.
--
--   It also packs a finite coordinate function into the recursive word representation used by tensor powers. The constructor identities state that reading a packed word recovers its input and that the joined coordinate has left-square grade $k$. These are coordinate data and projection identities only; no tensor restriction, value bound, entropy estimate, or induced family is asserted.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Section 3.5 (coarsening consecutive coordinate grades), Definition 3.7 (split distributions), and Definition 3.9 (restricted-splitting tensor power). This is an elementary coordinate-level helper derived from these definitions and the canonical fourth-power grading; it is not claimed as a named theorem of the paper.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Tactic

/-! Child fine-Z refinements preserve the coarse-Z profile of a fourth-power
parent. The statement uses genuine canonical coordinate fibers and the
public prescribedZWord predicate; no entropy or tensor-value assertion is
encoded in the hypotheses. -/

set_option autoImplicit false
set_option warningAsError true
open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
universe u

namespace MME.CoupledParentCompatibility

def packWord {ι : Type u} : (n : ℕ) → (Fin n → ι) → PowIndex ι n
  | 0, _ => PUnit.unit
  | n + 1, w => (w 0, packWord n (fun r => w r.succ))

theorem get_packWord {ι : Type u} (n : ℕ) (w : Fin n → ι) (r : Fin n) :
    PowIndex.get n (packWord n w) r = w r := by
  induction n with
  | zero => exact r.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) r
    · rfl
    · exact ih (fun j => w j.succ) j

/-- Actual coordinate fiber of the canonical fourth-power coarse Z class. -/
def FourthCoord (q : ℕ) (L : Fin 9) : Type u :=
  ULift.{u} {p : (Fin (q + 2) × Fin (q + 2)) ×
    (Fin (q + 2) × Fin (q + 2)) // StothersFourth.cwFourthPairGrade q p = L}

/-- The fine grade prescribed at the fourth-power level is the total grade
of its left *square* factor, not the finer left CW coordinate within it. -/
def fourthLeftGrade {q : ℕ} {L : Fin 9} (p : FourthCoord.{u} q L) : Fin 5 :=
  cwSquarePairGrade q p.down.1.1

def joinCoords (q : ℕ) (L : Fin 9) (kLeft kRight : Fin 5)
    (hsum : kLeft.val + kRight.val = L.val)
    (x : LiftedCoarsePair.{u} q kLeft)
    (y : LiftedCoarsePair.{u} q kRight) : FourthCoord.{u} q L :=
  ⟨⟨(x.down.1, y.down.1), by
    apply Fin.ext
    change (cwSquarePairGrade q x.down.1).val +
      (cwSquarePairGrade q y.down.1).val = L.val
    rw [x.down.2, y.down.2]
    exact hsum⟩⟩

theorem joined_left_grade (q : ℕ) (L : Fin 9) (kLeft kRight : Fin 5)
    (hsum : kLeft.val + kRight.val = L.val)
    (x : LiftedCoarsePair.{u} q kLeft)
    (y : LiftedCoarsePair.{u} q kRight) :
    fourthLeftGrade (joinCoords q L kLeft kRight hsum x y) = kLeft :=
  x.down.2


end MME.CoupledParentCompatibility


