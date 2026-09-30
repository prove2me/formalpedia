-- Prove2me | solution 1 for Hirsch.polynomial_edge_refinement_of_circuit_walks_of_high_carrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:29:29.491091+00:00
-- url     : https://prove2.me/submissions/4a4fecf5-12f7-48de-a20e-0b24bf20227a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Hirsch_common_face_diameter_of_dim_le_three
import Theorems.Thm_Hirsch_common_face_diameter_of_dim_ge_four
import Theorems.Thm_Hirsch_feasible_face_covered_sequence_route_bound
import Definitions.Def_Hirsch_circuit_model
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


theorem diamLE_pad_walk {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {m B : ℕ} (h : m ≤ B)
    {u v : E}
    (hP : ∃ w : ℕ → E, w 0 = u ∧ w m = v ∧
      ∀ j < m, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)) := by
  obtain ⟨w, hw0, hwm, hs⟩ := hP
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

theorem solution :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      4 ≤ d →
      Bornology.IsBounded (Hirsch.Hpoly a b) →
      Hirsch.RowPresentationIrredundant a b → Hirsch.StrictlyFeasibleRows a b →
      ∀ u ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
      ∀ L : ℕ, ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u → w L = v →
        (∀ j ≤ L, w j ∈ Hirsch.Hpoly a b) →
        (∀ j < L, w j = w (j + 1) ∨ Hirsch.RowCircuitStep a b (w j) (w (j + 1))) →
        (∃ j < L, 3 < HirschCommonFace.commonFaceDim a b (w j) (w (j + 1))) →
        ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
          q 0 = u ∧ q (C * (n + d) ^ k * L) = v ∧
          ∀ j < C * (n + d) ^ k * L,
            q j = q (j + 1) ∨
              Hirsch.Adj (Hirsch.Hpoly a b) (q j) (q (j + 1)) := by
  obtain ⟨Ch, kh, hhigh⟩ := Hirsch.common_face_diameter_of_dim_ge_four
  refine ⟨2 * (Ch + 1), kh + 1, ?_⟩
  intro d n a b hd4 hbd _hirr _hstrict u hu v hv L w hw0 hwL hfeas _hstep _hsome
  let F : Fin L → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => commonFace a b (w i.val) (w (i.val + 1))
  let M : ℕ := n + Ch * (n + d) ^ kh
  let B : Fin L → ℕ := fun _ => M
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
    by_cases hle : commonFaceDim a b (w i.val) (w (i.val + 1)) ≤ 3
    · have hraw :=
        common_face_diameter_of_dim_le_three a b (w i.val) (w (i.val + 1))
          hbd hle hne
      have hpad : n - commonFaceDim a b (w i.val) (w (i.val + 1)) ≤ M :=
        (Nat.sub_le _ _).trans (Nat.le_add_right n _)
      exact diamLE_mono (F i) hpad hraw
    · have hge : 4 ≤ commonFaceDim a b (w i.val) (w (i.val + 1)) := by omega
      have hraw :=
        hhigh d n a b (w i.val) (w (i.val + 1)) hbd hge hne
      have hpad : Ch * (n + d) ^ kh ≤ M := Nat.le_add_left _ n
      exact diamLE_mono (F i) hpad hraw
  have hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i := by
    intro k hk
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · exact commonFace_u_mem a b (w k) (w (k + 1)) (hfeas k (Nat.le_of_lt hk))
    · exact commonFace_x_mem a b (w k) (w (k + 1))
        (hfeas (k + 1) (Nat.succ_le_of_lt hk))
  have hroute :=
    feasible_face_covered_sequence_route_bound
      (Hpoly a b) F B hP hF hclosed hD w L hfeas
      (by simpa [hw0] using hu) (by simpa [hwL] using hv) hcover
  have hsum : (∑ i : Fin L, B i) = M * L := by
    simp [B, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  have hlen : M * L ≤ 2 * (Ch + 1) * (n + d) ^ (kh + 1) * L := by
    have hpos : 0 < n + d := by omega
    have hbase : n + d ≤ (n + d) ^ (kh + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero kh) (n + d)
    have hn : n ≤ (Ch + 1) * (n + d) ^ (kh + 1) :=
      (Nat.le_add_right n d).trans
        (hbase.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos Ch)))
    have hCpow : Ch * (n + d) ^ kh ≤ (Ch + 1) * (n + d) ^ (kh + 1) :=
      Nat.mul_le_mul (Nat.le_succ Ch)
        (Nat.pow_le_pow_right hpos (Nat.le_succ kh))
    have hM : M ≤ 2 * (Ch + 1) * (n + d) ^ (kh + 1) := by
      have hsum' := Nat.add_le_add hn hCpow
      have h2 :
          (Ch + 1) * (n + d) ^ (kh + 1) + (Ch + 1) * (n + d) ^ (kh + 1) =
            2 * (Ch + 1) * (n + d) ^ (kh + 1) := by ring
      exact hsum'.trans (le_of_eq h2)
    exact Nat.mul_le_mul_right L hM
  obtain ⟨q, hq0, hqB, hstepq⟩ := hroute
  have hq0u : q 0 = u := hq0.trans hw0
  have hqBv : q (M * L) = v := by
    simpa [hsum] using hqB.trans hwL
  have hstepM : ∀ j < M * L,
      q j = q (j + 1) ∨ Adj (Hpoly a b) (q j) (q (j + 1)) := by
    simpa [hsum] using hstepq
  exact diamLE_pad_walk hlen ⟨q, hq0u, hqBv, hstepM⟩

#print axioms solution
