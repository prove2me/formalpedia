-- Prove2me | Definitions.Def_Couret_RecohTernarySelector_13a2b1134dfc
-- name    : Couret_RecohTernarySelector_13a2b1134dfc
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:06:22.516209+00:00
-- url     : https://prove2.me/theorems/f2764c03-e7c2-4aa8-89bb-faf5849d205d
-- title:
--   Deterministic detection of three-torsion coordinates
-- statement:
--   A coordinate scan searches the cyclic product for a coordinate detecting a supplied three-torsion element, with an optional result and a step counter. The nonoptional selector uses proofs that the element is nonzero and killed by three to supply a valid primary coordinate. This supports a reproducible selected ternary probe.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTernarySelector.lean; source file SHA-256 80e6d82f0d714a0a990e4cb06a522f263602edb4a6af0908e1b5acc52eaa9c1f

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An executable coordinate selector for a supplied direction killed by three.
The search visits the labelled cyclic coordinates in increasing order and
returns the first nonzero coordinate whose modulus is divisible by three.
Only natural divisibility and equality in a cyclic group are tested.

The optional selector is defined on every input vector. The total selector
requires the direction to be nonzero and killed by three; its proof arguments
are erased during execution. Complex characters are used only to state the
semantic detection guarantee for the selected coordinate.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ)

/-- Scan an explicitly ordered list of coordinate labels. -/
def recohTernaryCoordinateScan
    (v : (i : Fin d) → ZMod (q i)) :
    List (Fin d) → Option (RecohPrimaryCoordinate q 3)
  | [] => none
  | i :: rest =>
      if h : 3 ∣ q i ∧ v i ≠ 0 then some ⟨i, h.1⟩
      else recohTernaryCoordinateScan v rest

/-- The number of coordinate predicates evaluated by the scan. -/
def recohTernaryCoordinateScanSteps
    (v : (i : Fin d) → ZMod (q i)) : List (Fin d) → ℕ
  | [] => 0
  | i :: rest =>
      if 3 ∣ q i ∧ v i ≠ 0 then 1
      else 1 + recohTernaryCoordinateScanSteps v rest

/-- The first usable ternary coordinate, in the order `0, ..., d - 1`. -/
def recohTernaryCoordinate?
    (v : (i : Fin d) → ZMod (q i)) :
    Option (RecohPrimaryCoordinate q 3) :=
  recohTernaryCoordinateScan q v (List.finRange d)

/-- Number of coordinate predicates evaluated by the complete selector. -/
def recohTernaryCoordinateSteps
    (v : (i : Fin d) → ZMod (q i)) : ℕ :=
  recohTernaryCoordinateScanSteps q v (List.finRange d)

theorem recoh_ternary_coordinate_scan_none_iff
    (v : (i : Fin d) → ZMod (q i)) (labels : List (Fin d)) :
    recohTernaryCoordinateScan q v labels = none ↔
      ∀ i ∈ labels, 3 ∣ q i → v i = 0 := by
  induction labels with
  | nil => simp [recohTernaryCoordinateScan]
  | cons i rest ih =>
      by_cases h : 3 ∣ q i ∧ v i ≠ 0
      · simp [recohTernaryCoordinateScan, h]
      · have hi : 3 ∣ q i → v i = 0 := by tauto
        simp [recohTernaryCoordinateScan, h, ih]
        exact fun _ => hi







theorem recoh_ternary_coordinate_none_iff
    (v : (i : Fin d) → ZMod (q i)) :
    recohTernaryCoordinate? q v = none ↔
      ∀ i : Fin d, 3 ∣ q i → v i = 0 := by
  simpa only [recohTernaryCoordinate?, List.mem_finRange, true_implies] using
    recoh_ternary_coordinate_scan_none_iff q v (List.finRange d)











variable [∀ i, NeZero (q i)]

/-- Failure on a vector killed by three is exactly the zero-vector case. -/
theorem recoh_ternary_coordinate_none_iff_zero
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) :
    recohTernaryCoordinate? q v = none ↔ v = 0 := by
  constructor
  · intro hs
    funext i
    by_cases hi : 3 ∣ q i
    · exact (recoh_ternary_coordinate_none_iff q v).mp hs i hi
    · apply recoh_cyclic_torsion_zero_of_coprime 3 (q i)
        (Nat.prime_three.coprime_iff_not_dvd.mpr hi) (v i)
      simpa only [Pi.smul_apply, Pi.zero_apply] using congrFun hv i
  · rintro rfl
    exact (recoh_ternary_coordinate_none_iff q 0).mpr (by simp)

theorem recoh_ternary_coordinate_exists
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) (hv0 : v ≠ 0) :
    ∃ i : RecohPrimaryCoordinate q 3, recohTernaryCoordinate? q v = some i := by
  cases hs : recohTernaryCoordinate? q v with
  | none => exact (hv0 ((recoh_ternary_coordinate_none_iff_zero q v hv).mp hs)).elim
  | some i => exact ⟨i, rfl⟩

/-- Extract the successful output using the nonzero torsion certificate. -/
def recohTernaryCoordinate
    (v : (i : Fin d) → ZMod (q i)) (hv : 3 • v = 0) (hv0 : v ≠ 0) :
    RecohPrimaryCoordinate q 3 :=
  (recohTernaryCoordinate? q v).get (by
    obtain ⟨i, hi⟩ := recoh_ternary_coordinate_exists q v hv hv0
    simp only [hi, Option.isSome_some])















end Couret.STROBO2TORS


