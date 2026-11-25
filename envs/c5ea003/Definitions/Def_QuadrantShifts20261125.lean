-- Prove2me | Definitions.Def_QuadrantShifts20261125
-- name    : QuadrantShifts20261125
-- status  : Definition
-- author  : @username
-- created : 2026-11-25T14:26:20.855596+00:00
-- url     : https://prove2.me/theorems/2cea7879-8fdf-5e36-b3fb-5fea3249530d
-- title:
--   Planar antidiagonal arrays and free quadrant shifts
-- statement:
--   The planar space consists of actual arrays obtained from strictly increasing sequences by antidiagonal enumeration. The shift maps translate array indices. The common-future relation is equality of some pair of translates. Binary configurations are free when distinct shifts give distinct translates.
-- source:
--   counterexamples-to-hypersmoothness.tex, Theorems A and B and Section 2. Supplied manuscript SHA-256 03093bc96808d915a59451a3d40499e92916b9ae136e5309dcc9065b86a4a603.

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.SetTheory.Cardinal.Continuum

set_option autoImplicit false

namespace HypersmoothCounterexamples

/-- Increasing enumerations of infinite subsets of the natural numbers. -/
abbrev Increasing := {s : ℕ → ℕ // StrictMono s}

/-- The first position of the `n`th antidiagonal in the enumeration. -/
def diagonalStart (n : ℕ) : ℕ := (n + 1).choose 2

/-- The planar sites are read by antidiagonal, then by second coordinate. -/
def siteIndex (v : ℕ × ℕ) : ℕ := diagonalStart (v.1 + v.2) + v.2

theorem diagonalStart_succ (n : ℕ) : diagonalStart (n + 1) = diagonalStart n + (n + 1) := by
  change ((n + 1) + 1).choose (1 + 1) = (n + 1).choose (1 + 1) + (n + 1)
  rw [Nat.choose_succ_succ' (n + 1) 1, Nat.choose_one_right, Nat.add_comm]

theorem diagonalStart_strictMono : StrictMono diagonalStart :=
  strictMono_nat_of_lt_succ fun n => by rw [diagonalStart_succ]; omega

theorem siteIndex_lt_iff {v w : ℕ × ℕ} :
    siteIndex v < siteIndex w ↔
      v.1 + v.2 < w.1 + w.2 ∨ (v.1 + v.2 = w.1 + w.2 ∧ v.2 < w.2) := by
  change diagonalStart (v.1 + v.2) + v.2 < diagonalStart (w.1 + w.2) + w.2 ↔ _
  rcases lt_trichotomy (v.1 + v.2) (w.1 + w.2) with h | h | h
  · have h' := diagonalStart_strictMono.monotone (show v.1 + v.2 + 1 ≤ w.1 + w.2 by omega)
    rw [diagonalStart_succ] at h'
    omega
  · rw [h]
    omega
  · have h' := diagonalStart_strictMono.monotone (show w.1 + w.2 + 1 ≤ v.1 + v.2 by omega)
    rw [diagonalStart_succ] at h'
    omega

theorem siteIndex_injective : Function.Injective siteIndex := by
  intro v w h
  have h₁ : ¬ (v.1 + v.2 < w.1 + w.2 ∨ (v.1 + v.2 = w.1 + w.2 ∧ v.2 < w.2)) :=
    fun hlt => (siteIndex_lt_iff.mpr hlt).ne h
  have h₂ : ¬ (w.1 + w.2 < v.1 + v.2 ∨ (w.1 + w.2 = v.1 + v.2 ∧ w.2 < v.2)) :=
    fun hlt => (siteIndex_lt_iff.mpr hlt).ne h.symm
  exact Prod.ext (by omega) (by omega)

theorem siteIndex_surjective : Function.Surjective siteIndex := by
  intro n
  induction n with
  | zero => exact ⟨(0, 0), rfl⟩
  | succ n ih =>
    obtain ⟨⟨i, j⟩, h⟩ := ih
    change diagonalStart (i+j) + j = n at h
    cases i with
    | zero =>
      refine ⟨(j+1, 0), ?_⟩
      simp only [siteIndex, Nat.zero_add, Nat.add_zero] at h ⊢
      rw [diagonalStart_succ]
      omega
    | succ i =>
      refine ⟨(i, j+1), ?_⟩
      change diagonalStart (i+(j+1)) + (j+1) = n+1
      rw [show i+(j+1) = i+1+j by omega]
      omega

theorem siteIndex_add_lt {v w : ℕ × ℕ} (a : ℕ × ℕ) (h : siteIndex v < siteIndex w) :
    siteIndex (v + a) < siteIndex (w + a) := by
  rw [siteIndex_lt_iff] at h ⊢
  change (v.1+a.1) + (v.2+a.2) < (w.1+a.1) + (w.2+a.2) ∨
    ((v.1+a.1) + (v.2+a.2) = (w.1+a.1) + (w.2+a.2) ∧ v.2+a.2 < w.2+a.2)
  omega

noncomputable def siteEquiv : (ℕ × ℕ) ≃ ℕ :=
  Equiv.ofBijective siteIndex ⟨siteIndex_injective, siteIndex_surjective⟩

/-- The array of labels corresponding to a strictly increasing enumeration. -/
def planarLabel (s : Increasing) (v : ℕ × ℕ) : ℕ := s.val (siteIndex v)

/-- Forward translation of an array on an additive index space. -/
def forward {I A : Type*} [Add I] (a : I) (x : I → A) : I → A := fun v => x (v + a)

/-- Two arrays have a common future when some forward translates coincide. -/
def CommonFuture {I A : Type*} [Add I] (x y : I → A) : Prop :=
  ∃ a b : I, forward a x = forward b y

def IncreasingRelation (s t : Increasing) : Prop :=
  ∃ a b : ℕ × ℕ, ∀ v, planarLabel s (v + a) = planarLabel t (v + b)

/-- The actual subspace of planar arrays with increasing antidiagonal labels. -/
abbrev PlanarArrays := {x : ℕ × ℕ → ℕ // x ∈ Set.range planarLabel}

theorem planarLabel_injective : Function.Injective planarLabel := by
  intro s t h
  apply Subtype.ext
  funext n
  obtain ⟨v, rfl⟩ := siteIndex_surjective n
  exact congrFun h v

noncomputable def increasingShift (a : ℕ × ℕ) (s : Increasing) : Increasing :=
  ⟨fun n => planarLabel s (siteEquiv.symm n + a), by
    intro n m h
    apply s.property
    apply siteIndex_add_lt
    change siteEquiv (siteEquiv.symm n) < siteEquiv (siteEquiv.symm m)
    simpa using h⟩

@[simp] theorem planarLabel_increasingShift (a : ℕ × ℕ) (s : Increasing) (v : ℕ × ℕ) :
    planarLabel (increasingShift a s) v = planarLabel s (v + a) := by
  change planarLabel s (siteEquiv.symm (siteEquiv v) + a) = _
  rw [Equiv.symm_apply_apply]

noncomputable def planarShift (a : ℕ × ℕ) (x : PlanarArrays) : PlanarArrays :=
  ⟨forward a x.val, by
    obtain ⟨s, hs⟩ := x.property
    refine ⟨increasingShift a s, ?_⟩
    rw [← hs]
    funext v
    exact planarLabel_increasingShift a s v⟩

def PlanarRelation (x y : PlanarArrays) : Prop := CommonFuture x.val y.val

/-- A configuration is free when different shift vectors give different translates. -/
def HasFreeTranslates {I A : Type*} [Add I] (x : I → A) : Prop :=
  Function.Injective (fun a : I => forward a x)

abbrev Quadrant (d : ℕ) := Fin d → ℕ
abbrev BinaryFreeSpace (d : ℕ) := {x : Quadrant d → Bool // HasFreeTranslates x}

def BinaryFreeRelation (d : ℕ) (x y : BinaryFreeSpace d) : Prop := CommonFuture x.val y.val

end HypersmoothCounterexamples


