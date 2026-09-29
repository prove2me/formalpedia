-- Prove2me | Definitions.Def_mme_recursive_yz_boundary_data
-- name    : mme_recursive_yz_boundary_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T12:40:25.720199+00:00
-- url     : https://prove2.me/theorems/effd457d-47f1-4500-a67a-607c145bb255
-- title:
--   Exact CW5 boundary profiles and matrix dimensions
-- statement:
--   An exact boundary profile records integer multiplicities of complete fine words, their total number of constituent positions, and their common grade. The other nonzero mode has the complementary fine-word profile; the zero mode has only the all-zero word. The explicit matrix dimension is the multinomial coefficient of the profile multiplied by 5 raised to the total number of grade-one positions. The three orientations refer to actual all-mode projected CW5 powers. The data contain no assumed tensor extraction or isomorphism.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Remark 6.1 and Theorem 6.2; exact integer-profile finite specialization.

import Definitions.Def_mme_recursive_yz_child_matrix_data
import Mathlib.Data.Fintype.EquivFin

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ.CWCells
  MME.DWZStep1Support
set_option autoImplicit false
universe u
namespace MME.RecursiveYZ.Boundary

abbrev Letters (ell : ℕ) := Fin (2 ^ (ell - 1)) → Fin 7

def labels {ell : ℕ} (x : Letters ell) : CompleteWord ell :=
  fun r ↦ cwSquareCoordGrade 5 (x r)

def flip (a : Fin 7) : Fin 7 := Equiv.swap 0 6 a
def flipLabel {ell : ℕ} (s : CompleteWord ell) : CompleteWord ell :=
  fun r ↦ ⟨2 - (s r).val, by omega⟩

def ones {ell : ℕ} (s : CompleteWord ell) : ℕ :=
  (Finset.univ.filter (fun r ↦ s r = 1)).card

abbrev Code (ell L : ℕ) (mu : CompleteWord ell → ℕ) :=
  {x : Fin L → Letters ell // ∀ s,
    Fintype.card {p : Fin L // labels (x p) = s} = mu s}

/-- Exact boundary profiles, with the free-mode shape and all integer multiplicities. -/
structure Profile (ell L : ℕ) where
  index : ℕ
  index_le : index ≤ 2 * 2 ^ (ell - 1)
  count : CompleteWord ell → ℕ
  total : ∑ s, count s = L
  supported : ∀ s, count s ≠ 0 → grade s = index

def Profile.dim {ell L : ℕ} (B : Profile ell L) : ℕ :=
  (L.factorial / ∏ s, (B.count s).factorial) *
    5 ^ (∑ s, B.count s * ones s)

def Profile.shape {ell L : ℕ} (B : Profile ell L) (z : Fin 3) : Fin 3 → ℕ :=
  if z = 0 then ![0, B.index, 2 * 2 ^ (ell - 1) - B.index]
  else if z = 1 then ![2 * 2 ^ (ell - 1) - B.index, 0, B.index]
  else ![B.index, 2 * 2 ^ (ell - 1) - B.index, 0]

def Profile.mu {ell L : ℕ} (B : Profile ell L) (z : Fin 3) :
    Fin 3 → CompleteWord ell → ℕ :=
  let zero := fun s : CompleteWord ell ↦ if s = (fun _ ↦ 0) then L else 0
  let other := fun s ↦ B.count (flipLabel s)
  if z = 0 then ![zero, B.count, other]
  else if z = 1 then ![other, zero, B.count]
  else ![B.count, other, zero]

def Profile.a {ell L : ℕ} (B : Profile ell L) (z : Fin 3) : ℕ :=
  if z = 1 then B.dim else 1
def Profile.b {ell L : ℕ} (B : Profile ell L) (z : Fin 3) : ℕ :=
  if z = 2 then B.dim else 1
def Profile.c {ell L : ℕ} (B : Profile ell L) (z : Fin 3) : ℕ :=
  if z = 0 then B.dim else 1

noncomputable def Profile.tensor {ell L : ℕ} (B : Profile ell L)
    (K : Type u) [Field K] (z : Fin 3) : TensorObj K 3 :=
  unbroken K 5 ell L (Equiv.refl _) (fun _ ↦ Unit.unit)
    (fun _ ↦ B.shape z) (fun i _ ↦ B.mu z i)

end MME.RecursiveYZ.Boundary


