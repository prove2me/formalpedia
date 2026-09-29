-- Prove2me | solution 1 for mme_exact_profile_boundary_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T18:38:42.150323+00:00
-- url     : https://prove2.me/submissions/e44bcf7a-9e84-4d9d-b057-e2e3a87a0529

import Mathlib
import Definitions.Def_mme_recursive_profiled_CW_data
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Boundary MME.CompleteSplit MME.ProfiledCW
open scoped Classical
set_option autoImplicit false


open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Boundary MME.CompleteSplit MME.ProfiledCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.BoundaryBuild

/-- The mode after the zero mode. -/
def nextMode (z : Fin 3) : Fin 3 := z + 1

theorem le_sum3 (g : Fin 3 → ℕ) (k : Fin 3) : g k ≤ g 0 + g 1 + g 2 := by
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega

/-- Exact boundary data on `L` blocks in `K` cells: every position of a cell carries the cell's
grade triple, one of whose modes is zero, and the words of the next mode have a prescribed
histogram. -/
structure Data (ell L K : ℕ) where
  cell : Fin L → Fin K
  zero : Fin K → Fin 3
  grade : Fin K → Fin 3 → ℕ
  total : ∀ c, grade c 0 + grade c 1 + grade c 2 = 2 * 2 ^ (ell - 1)
  zero_eq : ∀ c, grade c (zero c) = 0
  count : Fin K → CompleteWord ell → ℕ
  count_total : ∀ c, ∑ s, count c s = Fintype.card {p : Fin L // cell p = c}
  count_support : ∀ c s, count c s ≠ 0 → CWCells.grade s = grade c (nextMode (zero c))

variable {ell L K : ℕ}

/-- The exact all-mode profile described by the data. -/
noncomputable def Data.mu (D : Data ell L K) (i : Fin 3) (c : Fin K) (s : CompleteWord ell) : ℕ :=
  if i = D.zero c then (if s = (fun _ ↦ 0) then Fintype.card {p : Fin L // D.cell p = c} else 0)
  else if i = nextMode (D.zero c) then D.count c s
  else D.count c (flipLabel s)

/-- The canonical partition of the positions by cell. -/
noncomputable def Data.part (D : Data ell L K) : CWCells.Partition D.cell :=
  CWCells.Partition.canonical D.cell

theorem card_inst {T : Type} (i1 i2 : Fintype T) : @Fintype.card T i1 = @Fintype.card T i2 := by
  congr 1
  exact Subsingleton.elim _ _

theorem part_size (D : Data ell L K) (j : Fin D.part.parts) :
    D.part.size j = Fintype.card {p : Fin L // D.cell p = D.part.cells j} := by
  simp only [Data.part, CWCells.Partition.canonical]
  exact card_inst _ _

/-- The boundary profile of one cell. -/
noncomputable def Data.profile (D : Data ell L K) (j : Fin D.part.parts) :
    Boundary.Profile ell (D.part.size j) where
  index := D.grade (D.part.cells j) (nextMode (D.zero (D.part.cells j)))
  index_le := by
    have h := D.total (D.part.cells j)
    have hle := le_sum3 (D.grade (D.part.cells j)) (nextMode (D.zero (D.part.cells j)))
    omega
  count := D.count (D.part.cells j)
  total := by
    have h := D.count_total (D.part.cells j)
    rw [h, part_size D j]
  supported := fun s hs ↦ D.count_support _ s hs

/-- The predicate the boundary extraction acts on: exact grades and exact histograms. -/
noncomputable def Data.exact (D : Data ell L K) {N : ℕ} (hL : L * 2 ^ (ell - 1) = N) :
    Predicate N :=
  fun i x ↦ (∀ p, CWCells.grade (split (Equiv.refl (Fin L)) hL x p) = D.grade (D.cell p) i) ∧
    Useful D.cell (D.mu i) (split (Equiv.refl (Fin L)) hL x)

theorem shape_char (g : Fin 3 → ℕ) (tot : ℕ) (htot : g 0 + g 1 + g 2 = tot) (z : Fin 3)
    (hz : g z = 0) :
    g = (if z = 0 then ![0, g 1, tot - g 1]
      else if z = 1 then ![tot - g 2, 0, g 2] else ![g 0, tot - g 0, 0]) := by
  funext i
  match z, i with
  | 0, 0 => simp_all
  | 0, 1 => simp_all
  | 0, 2 => simp_all; omega
  | 1, 0 => simp_all; omega
  | 1, 1 => simp_all
  | 1, 2 => simp_all
  | 2, 0 => simp_all
  | 2, 1 => simp_all; omega
  | 2, 2 => simp_all

theorem shape_eq (D : Data ell L K) (j : Fin D.part.parts) :
    D.grade (D.part.cells j) = (D.profile j).shape (D.zero (D.part.cells j)) := by
  have htot := D.total (D.part.cells j)
  have hz := D.zero_eq (D.part.cells j)
  rw [shape_char (D.grade (D.part.cells j)) _ htot _ hz]
  obtain ⟨z, hzeq⟩ : ∃ z : Fin 3, D.zero (D.part.cells j) = z := ⟨_, rfl⟩
  rw [hzeq]
  match z with
  | 0 => simp [Boundary.Profile.shape, Data.profile, nextMode, hzeq]
  | 1 => simp [Boundary.Profile.shape, Data.profile, nextMode, hzeq]
  | 2 => simp [Boundary.Profile.shape, Data.profile, nextMode, hzeq]

theorem mu_eq (D : Data ell L K) (j : Fin D.part.parts) (i : Fin 3) :
    D.mu i (D.part.cells j) = (D.profile j).mu (D.zero (D.part.cells j)) i := by
  obtain ⟨z, hzeq⟩ : ∃ z : Fin 3, D.zero (D.part.cells j) = z := ⟨_, rfl⟩
  funext s
  simp only [Data.mu, Boundary.Profile.mu, Data.profile, hzeq, ← part_size D j]
  match z, i with
  | 0, 0 => simp [nextMode]
  | 0, 1 => simp [nextMode]
  | 0, 2 => simp [nextMode]
  | 1, 0 => simp [nextMode]
  | 1, 1 => simp [nextMode]
  | 1, 2 => simp [nextMode]
  | 2, 0 => simp [nextMode]
  | 2, 1 => simp [nextMode]
  | 2, 2 => simp [nextMode]

/-- The boundary end of exact data. -/
noncomputable def Data.end_ (D : Data ell L K) {N : ℕ} (hL : L * 2 ^ (ell - 1) = N) :
    BoundaryEnd ell N (D.exact hL) where
  L := L
  cells := K
  length := hL
  cell := D.cell
  shape := D.grade
  mu := D.mu
  partition := D.part
  profile := D.profile
  zeroMode := fun j ↦ D.zero (D.part.cells j)
  shapes := fun j ↦ shape_eq D j
  profiles := fun j i ↦ mu_eq D j i
  inside := fun i x h ↦ h

theorem dim_eq (D : Data ell L K) (j : Fin D.part.parts) :
    (D.profile j).a (D.zero (D.part.cells j)) * (D.profile j).b (D.zero (D.part.cells j)) *
      (D.profile j).c (D.zero (D.part.cells j)) = (D.profile j).dim := by
  obtain ⟨z, hzeq⟩ : ∃ z : Fin 3, D.zero (D.part.cells j) = z := ⟨_, rfl⟩
  rw [hzeq]
  match z with
  | 0 => simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]
  | 1 => simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]
  | 2 => simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

theorem end_dims (D : Data ell L K) {N : ℕ} (hL : L * 2 ^ (ell - 1) = N) :
    (D.end_ hL).a * (D.end_ hL).b * (D.end_ hL).c =
      ∏ c : Fin K, ((Fintype.card {p : Fin L // D.cell p = c}).factorial /
        ∏ s, (D.count c s).factorial) * 5 ^ (∑ s, D.count c s * Boundary.ones s) := by
  have hab : (D.end_ hL).a * (D.end_ hL).b * (D.end_ hL).c =
      ∏ j, (D.profile j).dim := by
    show (∏ j, (D.profile j).a _) * (∏ j, (D.profile j).b _) * (∏ j, (D.profile j).c _) = _
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ ↦ dim_eq D j)
  rw [hab, ← Equiv.prod_comp D.part.cells (fun c ↦ _)]
  refine Finset.prod_congr rfl (fun j _ ↦ ?_)
  show ((D.part.size j).factorial / ∏ s, (D.count (D.part.cells j) s).factorial) *
      5 ^ (∑ s, D.count (D.part.cells j) s * Boundary.ones s) = _
  rw [part_size D j]

end MME.BoundaryBuild


open MME.BoundaryBuild in
theorem solution {ell N L K : ℕ} (hL : L * 2 ^ (ell - 1) = N)
    (cell : Fin L → Fin K) (zero : Fin K → Fin 3) (grade : Fin K → Fin 3 → ℕ)
    (htotal : ∀ c, grade c 0 + grade c 1 + grade c 2 = 2 * 2 ^ (ell - 1))
    (hzero : ∀ c, grade c (zero c) = 0)
    (count : Fin K → CompleteWord ell → ℕ)
    (hcount : ∀ c, ∑ s, count c s = Fintype.card {p : Fin L // cell p = c})
    (hsupport : ∀ c s, count c s ≠ 0 → CWCells.grade s = grade c (zero c + 1)) :
    ∃ B : BoundaryEnd ell N (fun i x ↦
        (∀ p, CWCells.grade (split (Equiv.refl (Fin L)) hL x p) = grade (cell p) i) ∧
          Useful cell (fun c s ↦
            if i = zero c then (if s = (fun _ ↦ 0) then Fintype.card {p : Fin L // cell p = c} else 0)
            else if i = zero c + 1 then count c s else count c (flipLabel s))
            (split (Equiv.refl (Fin L)) hL x)),
      B.a * B.b * B.c = ∏ c : Fin K, ((Fintype.card {p : Fin L // cell p = c}).factorial /
        ∏ s, (count c s).factorial) * 5 ^ (∑ s, count c s * Boundary.ones s) := by
  classical
  refine ⟨(Data.end_ ⟨cell, zero, grade, htotal, hzero, count, hcount, hsupport⟩ hL), ?_⟩
  exact end_dims _ hL
