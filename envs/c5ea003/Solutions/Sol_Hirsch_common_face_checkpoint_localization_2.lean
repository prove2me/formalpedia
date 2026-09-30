-- Prove2me | solution 2 for Hirsch.common_face_checkpoint_localization
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:03:54.076427+00:00
-- url     : https://prove2.me/submissions/3714b216-90ad-422c-b5a2-919c6f06df79

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

variable {d n : ℕ}

open HirschCommonFace

/-- Rows tight at the first point but not the second. -/
def sourceOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, x⟫ = b i ∧ ⟪a i, y⟫ ≠ b i)

/-- Rows tight at the second point but not the first. -/
def targetOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, x⟫ ≠ b i ∧ ⟪a i, y⟫ = b i)

/-- Nonzero rows annihilating a direction. -/
def directionNeutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, g⟫ = 0)

/-- Rank-nullity estimate: shrinking the row set can enlarge the kernel by
at most the number of deleted rows. -/
theorem ker_finrank_le_of_row_subset
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (S T : Finset (Fin n)) (hST : S ⊆ T) :
    Module.finrank ℝ (rowEvalMap a S).ker ≤
      Module.finrank ℝ (rowEvalMap a T).ker + (T \ S).card := by
  classical
  let D := T \ S
  let φ : (rowEvalMap a S).ker →ₗ[ℝ] (D → ℝ) :=
    { toFun := fun y i => ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c y
        funext i
        simp [inner_smul_right] }
  have hincl : (rowEvalMap a T).ker ≤ (rowEvalMap a S).ker := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    funext i
    exact congrFun hy ⟨i.1, hST i.2⟩
  have hφrank := φ.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ φ.range ≤ D.card := by
    have : Module.finrank ℝ (D → ℝ) = D.card := by simp [Fintype.card_coe]
    exact (Submodule.finrank_le φ.range).trans (le_of_eq this)
  have hkerφ_le : Module.finrank ℝ φ.ker ≤
      Module.finrank ℝ (rowEvalMap a T).ker := by
    let ψ : φ.ker →ₗ[ℝ] (rowEvalMap a T).ker :=
      { toFun := fun y =>
          ⟨(y.1 : EuclideanSpace ℝ (Fin d)), by
            rw [LinearMap.mem_ker]
            funext i
            have hiT : i.1 ∈ T := i.2
            by_cases hiS : i.1 ∈ S
            · have hS0 : rowEvalMap a S (y.1 : EuclideanSpace ℝ (Fin d)) = 0 :=
                LinearMap.mem_ker.1 y.1.property
              exact congrFun hS0 ⟨i.1, hiS⟩
            · have hiD : i.1 ∈ D := Finset.mem_sdiff.2 ⟨hiT, hiS⟩
              have hφ : φ y.1 = 0 := LinearMap.mem_ker.1 y.property
              exact congrFun hφ ⟨i.1, hiD⟩⟩
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hinj : Function.Injective ψ := by
      intro y z hyz
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : (rowEvalMap a T).ker =>
        (w : EuclideanSpace ℝ (Fin d))) hyz
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hdom : Module.finrank ℝ (rowEvalMap a S).ker =
      Module.finrank ℝ φ.range + Module.finrank ℝ φ.ker := hφrank.symm
  have h1 : Module.finrank ℝ (rowEvalMap a S).ker ≤
      D.card + Module.finrank ℝ φ.ker := by
    have := hdom.le.trans (Nat.add_le_add_right hrange _)
    simpa [Nat.add_comm] using this
  have h2 : D.card + Module.finrank ℝ φ.ker ≤
      Module.finrank ℝ (rowEvalMap a T).ker + D.card := by
    simpa [Nat.add_comm] using Nat.add_le_add_left hkerφ_le D.card
  exact h1.trans h2

theorem commonFaceDim_le_sourceOnly_add_sourceNullity
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x y ≤
      (sourceOnlyRows a b x y).card + commonFaceDim a b x x := by
  classical
  have hsub : commonSourceRows a b x y ⊆ commonSourceRows a b x x := by
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ i, h.1, h.2.1, h.2.1⟩
  have hdiff :
      commonSourceRows a b x x \ commonSourceRows a b x y =
        sourceOnlyRows a b x y := by
    ext i
    simp only [commonSourceRows, sourceOnlyRows, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hai, hix, _⟩, hn⟩
      exact ⟨hai, hix, fun hiy => hn ⟨hai, hix, hiy⟩⟩
    · rintro ⟨hai, hix, hiy⟩
      exact ⟨⟨hai, hix, hix⟩, fun h => hiy h.2.2⟩
  have h := ker_finrank_le_of_row_subset a
    (commonSourceRows a b x y) (commonSourceRows a b x x) hsub
  change commonFaceDim a b x y ≤ commonFaceDim a b x x +
    (commonSourceRows a b x x \ commonSourceRows a b x y).card at h
  rw [hdiff] at h
  simpa [Nat.add_comm] using h

theorem commonFaceDim_le_targetOnly_add_targetNullity
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    commonFaceDim a b x y ≤
      (targetOnlyRows a b x y).card + commonFaceDim a b y y := by
  classical
  have hC : commonSourceRows a b y x = commonSourceRows a b x y := by
    ext i
    simp [commonSourceRows, and_comm, and_left_comm, and_assoc]
  have hdim : commonFaceDim a b y x = commonFaceDim a b x y := by
    unfold commonFaceDim commonDirection
    rw [hC]
  have hS : sourceOnlyRows a b y x = targetOnlyRows a b x y := by
    ext i
    simp [sourceOnlyRows, targetOnlyRows, and_comm, and_left_comm, and_assoc]
  have h := commonFaceDim_le_sourceOnly_add_sourceNullity a b y x
  rw [hdim, hS] at h
  exact h

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    2 * commonFaceDim a b x y + d ≤
      n + commonFaceDim a b x x + commonFaceDim a b y y +
        ((d - 1) -
          Module.finrank ℝ
            (rowEvalMap a
              (Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).range) + 1 := by
  classical
  let S := sourceOnlyRows a b x y
  let T := targetOnlyRows a b x y
  let Z := directionNeutralRows a (y - x)
  have hS : commonFaceDim a b x y ≤ S.card + commonFaceDim a b x x :=
    commonFaceDim_le_sourceOnly_add_sourceNullity a b x y
  have hT : commonFaceDim a b x y ≤ T.card + commonFaceDim a b y y :=
    commonFaceDim_le_targetOnly_add_targetNullity a b x y
  have hZrank : Module.finrank ℝ (rowEvalMap a Z).range ≤ Z.card := by
    calc
      _ ≤ Module.finrank ℝ (Z → ℝ) := Submodule.finrank_le _
      _ = Z.card := by simp [Fintype.card_coe]
  have hZ : d ≤ Z.card +
      ((d - 1) - Module.finrank ℝ (rowEvalMap a Z).range) + 1 := by
    have harith : ∀ d r z : ℕ, r ≤ z → d ≤ z + ((d - 1) - r) + 1 := by
      intros; omega
    exact harith d _ _ hZrank
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have hs := (Finset.mem_filter.1 hiS).2
    have ht := (Finset.mem_filter.1 hiT).2
    exact ht.2.1 hs.2.1
  have hSZ : Disjoint S Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiZ
    have hs := (Finset.mem_filter.1 hiS).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, y - x⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hyEq : ⟪a i, y⟫ = b i := by linarith [hs.2.1]
    exact hs.2.2 hyEq
  have hTZ : Disjoint T Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiT hiZ
    have ht := (Finset.mem_filter.1 hiT).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, y - x⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hxEq : ⟪a i, x⟫ = b i := by linarith [ht.2.2]
    exact ht.2.1 hxEq
  have hSTZ : Disjoint (S ∪ T) Z := Finset.disjoint_union_left.2 ⟨hSZ, hTZ⟩
  have hcount : (S ∪ T ∪ Z).card ≤ n := by
    calc
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (by simp)
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hSTZ,
    Finset.card_union_of_disjoint hST] at hcount
  have harith : ∀ h d n s t z p q δ : ℕ,
      h ≤ s + p → h ≤ t + q → d ≤ z + δ + 1 → s + t + z ≤ n →
      2 * h + d ≤ n + p + q + δ + 1 := by
    intros; omega
  simpa [Z, directionNeutralRows] using
    harith _ _ _ _ _ _ _ _ _ hS hT hZ hcount

#print axioms solution
