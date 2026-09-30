-- Prove2me | solution 2 for Hirsch.common_face_sequence_route_bound_of_dim_le_three
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T01:58:57.399158+00:00
-- url     : https://prove2.me/submissions/bae4666c-56c3-4296-963a-fafb1eed9ac1

import Theorems.Thm_Hirsch_common_face_diameter_of_dim_le_three
import Theorems.Thm_Hirsch_feasible_face_covered_sequence_route_bound
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Hirsch

noncomputable section

variable {d n : ℕ}

open HirschCommonFace

theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m L : ℕ} (h : m ≤ L) (hP : DiamLE P m) : DiamLE P L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwm, hs⟩ := hP u hu v hv
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

theorem hpoly_isClosed
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  have heq : Hpoly a b = ⋂ i : Fin n, {x | ⟪a i, x⟫ ≤ b i} := by
    ext x
    simp [Hpoly]
  rw [heq]
  exact isClosed_iInter fun i =>
    isClosed_le (innerSL ℝ (a i)).continuous continuous_const

theorem hpoly_isCompact_of_bounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    IsCompact (Hpoly a b) := by
  have hcl := hpoly_isClosed a b
  simpa [hcl.closure_eq] using hbd.isCompact_closure

theorem commonFace_isClosed
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    IsClosed (commonFace a b u x) := by
  let S := commonSourceRows a b u x
  have htight :
      {y : EuclideanSpace ℝ (Fin d) |
          ∀ i, i ∈ S → ⟪a i, y⟫ = b i} =
        ⋂ i ∈ S, {y | ⟪a i, y⟫ = b i} := by
    ext y
    simp
  have h2 : IsClosed {y : EuclideanSpace ℝ (Fin d) |
      ∀ i, i ∈ S → ⟪a i, y⟫ = b i} := by
    rw [htight]
    exact isClosed_biInter fun i _ =>
      isClosed_eq (innerSL ℝ (a i)).continuous continuous_const
  have heq : commonFace a b u x =
      Hpoly a b ∩ {y | ∀ i, i ∈ S → ⟪a i, y⟫ = b i} := rfl
  rw [heq]
  exact (hpoly_isClosed a b).inter h2

theorem commonFace_u_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    u ∈ commonFace a b u x := by
  refine ⟨hu, ?_⟩
  intro i hiC
  exact (Finset.mem_filter.1 hiC).2.2.1

theorem commonFace_x_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) :
    x ∈ commonFace a b u x := by
  refine ⟨hx, ?_⟩
  intro i hiC
  exact (Finset.mem_filter.1 hiC).2.2.2

/-- CommonFace_isExtreme needs the real left_mem field; the stub above is
wrong for Mathlib 4.30. The full proof is the supporting-hyperplane argument. -/
theorem commonFace_isExtreme'
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    IsExtreme ℝ (Hpoly a b) (commonFace a b u x) := by
  refine ⟨fun y hy => hy.1, ?_⟩
  intro p hp q hq z hz hzopen
  refine ⟨hp, ?_⟩
  intro i hiC
  have hztight : ⟪a i, z⟫ = b i := hz.2 i hiC
  have hp_le := hp i
  have hq_le := hq i
  obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
  have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
    rw [← hzcomb]
    simp [inner_add_right, inner_smul_right]
  by_contra hptight
  have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
  have h1 : α * ⟪a i, p⟫ < α * b i :=
    mul_lt_mul_of_pos_left hp_lt hα
  have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
    mul_le_mul_of_nonneg_left hq_le hβ.le
  have hb : α * b i + β * b i = b i := by
    rw [← add_mul, hαβ, one_mul]
  linarith

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ Hpoly a b)
    (h0 : w 0 ∈ Set.extremePoints ℝ (Hpoly a b))
    (hL : w L ∈ Set.extremePoints ℝ (Hpoly a b))
    (hdim : ∀ k < L, commonFaceDim a b (w k) (w (k + 1)) ≤ 3) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (n * L) = w L ∧
      ∀ r < n * L,
        q r = q (r + 1) ∨ Adj (Hpoly a b) (q r) (q (r + 1)) := by
  let F : Fin L → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => commonFace a b (w i.val) (w (i.val + 1))
  let B : Fin L → ℕ := fun _ => n
  have hP := hpoly_isCompact_of_bounded a b hbd
  have hF : ∀ i : Fin L, IsExtreme ℝ (Hpoly a b) (F i) :=
    fun i => commonFace_isExtreme' a b (w i.val) (w (i.val + 1))
  have hclosed : ∀ i : Fin L, IsClosed (F i) :=
    fun i => commonFace_isClosed a b (w i.val) (w (i.val + 1))
  have hD : ∀ i : Fin L, DiamLE (F i) (B i) := by
    intro i
    have hne : (commonFace a b (w i.val) (w (i.val + 1))).Nonempty :=
      ⟨w i.val, commonFace_u_mem a b (w i.val) (w (i.val + 1))
        (hfeas i.val (Nat.le_of_lt i.isLt))⟩
    have hdimi : commonFaceDim a b (w i.val) (w (i.val + 1)) ≤ 3 :=
      hdim i.val i.isLt
    have hraw :=
      common_face_diameter_of_dim_le_three a b (w i.val) (w (i.val + 1))
        hbd hdimi hne
    have hle : n - commonFaceDim a b (w i.val) (w (i.val + 1)) ≤ n :=
      Nat.sub_le _ _
    exact diamLE_mono (F i) hle hraw
  have hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i := by
    intro k hk
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · exact commonFace_u_mem a b (w k) (w (k + 1))
        (hfeas k (Nat.le_of_lt hk))
    · exact commonFace_x_mem a b (w k) (w (k + 1))
        (hfeas (k + 1) (Nat.succ_le_of_lt hk))
  have hroute :=
    feasible_face_covered_sequence_route_bound
      (Hpoly a b) F B hP hF hclosed hD w L hfeas h0 hL hcover
  have hsum : (∑ i : Fin L, B i) = n * L := by
    simp [B, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  simpa [hsum] using hroute

#print axioms solution
