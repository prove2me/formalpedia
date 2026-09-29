-- Prove2me | solution 1 for mme_entropy_regional_scalar_step_sharp_boundary_volume
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T06:47:32.697708+00:00
-- url     : https://prove2.me/submissions/433ce830-5ff7-43d0-886d-47155f24955a

import Definitions.Def_mme_entropy_regional_CW_recipe
import Theorems.Thm_mme_recursive_profiled_CW_boundary_end
import Theorems.Thm_mme_flatteningRank_MMObj_ab
import Theorems.Thm_mme_flatteningRank_MMObj_bc
import Definitions.Def_mme_flattening

section

open BigOperators MME MME.ProfiledCW MME.RegionRealization MME.RecursiveYZ
open MME.CompleteSplit MME.RecursiveThinSplit

namespace ScalarRegionalStep

def parent : Fin 1 → Fin 3 → ℕ := fun _ ↦ ![4, 0, 0]
abbrev counts : Fin 1 → ℕ := fun _ ↦ 1

def left : Split 2 (parent 0) := ⟨![2, 0, 0], by decide⟩

lemma split_eq (r : Fin 1) (a : Split 2 (parent r)) : a = left := by
  have hr : r = 0 := Subsingleton.elim _ _
  subst r
  apply Subtype.ext
  funext i
  have h1 := a.property.2 1
  have h2 := a.property.2 2
  have hs := a.property.1
  simp [parent] at h1 h2
  fin_cases i <;> apply Fin.ext <;> simp [left] <;> omega

def positions : Fin 2 ≃ Position counts where
  toFun p := ⟨0, 0, p⟩
  invFun p := p.2.2
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨r, t, h⟩
    have hr : r = 0 := Subsingleton.elim _ _
    have ht : t = 0 := Subsingleton.elim _ _
    subst r
    subst t
    rfl

def hashPositions : Fin 1 ≃ (r : Fin 1) × Fin (counts r) where
  toFun _ := ⟨0, 0⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv p := by
    rcases p with ⟨r, t⟩
    fin_cases r
    fin_cases t
    rfl

def mu (i : Fin 3) (_ : Cell 2 1 parent) (w : CompleteWord 1) : ℕ :=
  if w 0 = left.val i then 2 else 0

lemma word_eq (w : CompleteWord 1) : w = fun _ ↦ w 0 := by
  funext r
  fin_cases r
  rfl

/-- A valid two-position regional step supported on the scalar split `(2,0,0)`. -/
noncomputable def step : IntegerStep 1 2 (fun _ _ ↦ True) where
  half := 2
  R := 1
  parent := parent
  n := counts
  total := by intro r; rfl
  half_eq := by norm_num
  m := fun _ _ ↦ 1
  N := 0
  hashPositions := hashPositions
  L := 2
  positions := positions
  length := by norm_num
  mu := mu
  mass := by
    intro i c
    classical
    change (∑ w : CompleteWord 1, mu i c w) = 2
    rw [Finset.sum_eq_single (fun _ ↦ left.val i)]
    · simp [mu]
    · intro w _ hw
      have hn : w 0 ≠ left.val i := by
        intro h
        apply hw
        rw [word_eq w, h]
      simp [mu, hn]
    · simp
  support := by
    intro i c w hw
    have hc := split_eq c.1 c.2
    have h : w 0 = left.val i := by
      by_contra h
      simp [mu, h] at hw
    simp [h, hc]
  boundary := by
    constructor
    · intro c hc w
      rw [split_eq c.1 c.2] at hc
      have hh : Fin.rev (w 0) = (2 : Fin 3) ↔ w 0 = 0 := by
        constructor <;> intro h <;> apply Fin.ext <;>
          have := congrArg Fin.val h <;> simp [Fin.rev] at * <;> omega
      simp [mu, left, hh]
    constructor
    · intro c hc
      rw [split_eq c.1 c.2] at hc
      norm_num [left] at hc
    · intro c hc w
      have hh : Fin.rev (w 0) = (2 : Fin 3) ↔ w 0 = 0 := by
        constructor <;> intro h <;> apply Fin.ext <;>
          have := congrArg Fin.val h <;> simp [Fin.rev] at * <;> omega
      simp [mu, left, hh]
  reference := fun _ _ ↦ left
  reference_target := by
    classical
    simp only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and]
    intro r a
    rw [split_eq r a]
    simp [RecursiveThinSplit.count]
  minimum := 1
  repairScale := 2
  minimum_pos := by decide
  repairScale_gt_one := by decide
  parent_size := by intro r; rfl
  split_divisible := by simp
  epsilon := 100
  epsilon_pos := by norm_num
  size_test := by norm_num [CompleteWord, Fintype.card_fun]
  source_inside := by intros; trivial

theorem output_scalar (i : Fin 3) (x : FineWord 2)
    (h : step.output i x) : x = fun _ ↦ left.val i := by
  funext r
  apply Fin.ext
  have hg := h.1 (positions r)
  fin_cases i <;> fin_cases r <;>
    simpa [step, positions, split, fullCell, complement, left, parent,
      Fin.sum_univ_succ] using hg

theorem scalar_output (i : Fin 3) : step.output i (fun _ ↦ left.val i) := by
  classical
  constructor
  · intro p
    rcases p with ⟨r, t, h⟩
    fin_cases r
    fin_cases t
    fin_cases h <;> fin_cases i <;>
      simp [step, positions, split, fullCell, complement, left, parent]
  · intro c w
    rcases c with ⟨r, a⟩
    have ha := split_eq r a
    fin_cases r
    subst a
    have hc (p : Position counts) :
        fullCell step.total step.reference p = ⟨(0 : Fin 1), left⟩ := by
      rcases p with ⟨r, t, h⟩
      fin_cases r
      dsimp only [fullCell, step]
      apply Sigma.ext (by rfl)
      apply heq_of_eq
      exact split_eq _ _
    change RecursiveYZ.count (fullCell step.total step.reference)
      (ProfiledCW.split step.positions step.length (fun _ ↦ left.val i))
      ⟨(0 : Fin 1), left⟩ w = mu i ⟨(0 : Fin 1), left⟩ w
    simp only [RecursiveYZ.count, hc, true_and]
    change (Finset.univ.filter (fun _ : Position counts ↦
      (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) = w)).card = mu i ⟨0, left⟩ w
    have he : (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) = w ↔
        w 0 = left.val i := by
      constructor
      · intro h
        exact (congrFun h 0).symm
      · intro h
        rw [word_eq w, h]
    by_cases h : w 0 = left.val i
    · have hf := he.mpr h
      rw [Finset.filter_eq_self.mpr (fun _ _ ↦ hf)]
      simp [h, mu, Position, Fintype.card_sigma]
    · have hf : (fun _ : Fin (2 ^ (1 - 1)) ↦ left.val i) ≠ w :=
        fun hh ↦ h (he.mp hh)
      rw [Finset.filter_eq_empty_iff.mpr (fun _ _ ↦ hf)]
      simp [h, mu]

/-- Each mode admits exactly its constant scalar word. -/
theorem output_iff (i : Fin 3) (x : FineWord 2) :
    step.output i x ↔ x = fun _ ↦ left.val i := by
  constructor
  · exact output_scalar i x
  · rintro rfl
    exact scalar_output i

end ScalarRegionalStep



end
section

open MME MME.ProfiledCW MME.TensorObj MME.RegionRealization Module
set_option autoImplicit false

namespace ScalarRegionalStep

def coordinate (i : Fin 3) : Coordinate 2 := fun _ ↦
  ULift.up (if i = 0 then 6 else 0)

lemma coordinate_unique (i : Fin 3) (x : Coordinate 2)
    (hx : step.output i (fine x)) : x = coordinate i := by
  have h := output_scalar i (fine x) hx
  funext r
  apply ULift.ext
  apply Fin.ext
  have hr := congrFun h r
  fin_cases i <;>
    simp [fine, left, cwSquareCoordGrade, coordinate] at * <;>
    split_ifs at hr <;> simp_all

/-- The scalar regional output spans at most one coordinate in each mode. -/
theorem mode_finrank_le_one (K : Type) [Field K] (i : Fin 3) :
    finrank K ((tensor K step.output).V i) ≤ 1 := by
  classical
  let b := canonical K 2 i
  let S : Submodule K ((raw K 2).V i) :=
    Submodule.span K (b '' {x | (if step.output i (fine x) then (0 : Fin 2) else 1) = 0})
  change finrank K S ≤ 1
  have hs : S ≤ Submodule.span K {b (coordinate i)} := by
    apply Submodule.span_mono
    rintro _ ⟨x, hx, rfl⟩
    have hx' : step.output i (fine x) := by
      by_contra hn
      simp [hn] at hx
    rw [coordinate_unique i x hx']
    exact Set.mem_singleton _
  apply (Submodule.finrank_mono hs).trans
  simpa using finrank_span_le_card (R := K) {b (coordinate i)}

/-- Flattening ranks cannot exceed one when all mode spaces have dimension at most one. -/
theorem flattening_rank_le_one (K : Type) [Field K] (σ : MME.Split (Fin 3)) :
    flatteningRank σ (tensor K step.output) ≤ 1 := by
  classical
  let X := tensor K step.output
  let b := Basis.piTensorProduct (fun i : Sc σ ↦ Free.chooseBasis K (X.V i))
  haveI := Module.Finite.of_basis b
  have hd : finrank K (PiTensorProduct K (fun i : Sc σ ↦ X.V i)) ≤ 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
    apply Finset.prod_le_one (fun _ _ ↦ Nat.zero_le _)
    intro i _
    rw [← Module.finrank_eq_card_basis (Free.chooseBasis K (X.V i))]
    exact mode_finrank_le_one K i
  exact (Submodule.finrank_le _).trans hd

/-- No matrix block of volume greater than one can be extracted from this output. -/
theorem matrix_volume_le_one (a b c : ℕ)
    (h : Restrict (MMObj ℚ a b c) (tensor ℚ step.output)) : a * b * c ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  by_cases hc : c = 0
  · simp [hc]
  have ha' : 1 ≤ a := by omega
  have hb' : 1 ≤ b := by omega
  have hc' : 1 ≤ c := by omega
  have hab := (mme_flatteningRank_MMObj_ab (K := ℚ) a b c hc').trans
    ((flatteningRank_mono _ h).trans (flattening_rank_le_one ℚ _))
  have hbc := (mme_flatteningRank_MMObj_bc (K := ℚ) a b c ha').trans
    ((flatteningRank_mono _ h).trans (flattening_rank_le_one ℚ _))
  have ha1 : a = 1 := by nlinarith
  have hb1 : b = 1 := by nlinarith
  have hc1 : c = 1 := by nlinarith
  simp [ha1, hb1, hc1]

theorem boundary_volume_le_one (B : BoundaryEnd 1 2 step.output) :
    B.a * B.b * B.c ≤ 1 :=
  matrix_volume_le_one B.a B.b B.c (mme_recursive_profiled_CW_boundary_end B)

theorem boundary_match_false : ¬ (∀ (lower : ℕ)
    (S : IntegerStep lower 2 (fun _ _ ↦ True)),
    ∃ B : BoundaryEnd lower 2 S.output,
      B.a * B.b * B.c = 25 ∧ 1 ≤ B.a * B.b * B.c) := by
  intro h
  obtain ⟨B, hB, _⟩ := h 1 step
  have := boundary_volume_le_one B
  omega

end ScalarRegionalStep




end
section

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.RegionRealization
set_option autoImplicit false

namespace ScalarRegionalStep

def zeroProfile : Boundary.Profile 1 2 where
  index := 0
  index_le := by decide
  count := fun w ↦ if w = (fun _ ↦ 0) then 2 else 0
  total := by
    classical
    simp
  supported := by
    intro w hw
    have h : w = fun _ ↦ 0 := by simpa using hw
    subst w
    simp [CWCells.grade]

def scalarPartition : CWCells.Partition (fun _ : Fin 2 ↦ (0 : Fin 1)) where
  parts := 1
  cells := Equiv.refl _
  size := fun _ ↦ 2
  fiber := fun _ ↦ {
    toFun := fun p ↦ ⟨p, Subsingleton.elim _ _⟩
    invFun := Subtype.val
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- The scalar step has a nonempty boundary realization of volume one. -/
def scalarBoundary : BoundaryEnd 1 2 step.output where
  L := 2
  cells := 1
  length := by norm_num
  cell := fun _ ↦ 0
  shape := fun _ ↦ zeroProfile.shape 1
  mu := fun i _ ↦ zeroProfile.mu 1 i
  partition := scalarPartition
  profile := fun _ ↦ zeroProfile
  zeroMode := fun _ ↦ 1
  shapes := by intro j; rfl
  profiles := by intro j i; rfl
  inside := by
    intro i x hx
    apply (output_iff i x).mpr
    funext r
    apply Fin.ext
    have h := hx.1 r
    fin_cases i <;> fin_cases r <;>
      simpa [CWCells.grade, ProfiledCW.split, Boundary.Profile.shape, zeroProfile, left] using h

theorem scalarBoundary_volume : scalarBoundary.a * scalarBoundary.b * scalarBoundary.c = 1 := by
  classical
  simp [BoundaryEnd.a, BoundaryEnd.b, BoundaryEnd.c, scalarBoundary, scalarPartition,
    Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c, Boundary.Profile.dim,
    zeroProfile, Boundary.ones, apply_ite]

end ScalarRegionalStep


end

theorem solution : ∃ S : MME.RegionRealization.IntegerStep 1 2 (fun _ _ ↦ True),
    (∃ B : MME.ProfiledCW.BoundaryEnd 1 2 S.output, B.a * B.b * B.c = 1) ∧
    ∀ B : MME.ProfiledCW.BoundaryEnd 1 2 S.output, B.a * B.b * B.c ≤ 1 := by
  refine ⟨ScalarRegionalStep.step, ?_, ?_⟩
  · exact ⟨ScalarRegionalStep.scalarBoundary, ScalarRegionalStep.scalarBoundary_volume⟩
  · exact ScalarRegionalStep.boundary_volume_le_one

#print axioms solution
