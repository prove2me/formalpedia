-- Prove2me | solution 1 for Hirsch.row_circuit_step_adj_of_common_face_dim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T23:25:52.282687+00:00
-- url     : https://prove2.me/submissions/cffbbaeb-ace8-4ab6-9659-9ce45700cc14

import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

variable {d n : ℕ}

/-- The intersection of a polytope with any collection of its supporting
hyperplanes is an extreme subset. -/
theorem commonFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    IsExtreme ℝ (Hpoly a b) (HirschCommonFace.commonFace a b u x) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    intro i hiC
    have hztight : ⟪a i, z⟫ = b i := hz.2 i hiC
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
    have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hzcomb]
      simp [inner_add_right, inner_smul_right]
    have hαpos : 0 < α := hα
    have hβnonneg : 0 ≤ β := hβ.le
    by_contra hptight
    have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
    have h1 : α * ⟪a i, p⟫ < α * b i :=
      mul_lt_mul_of_pos_left hp_lt hαpos
    have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
      mul_le_mul_of_nonneg_left hq_le hβnonneg
    have hb : α * b i + β * b i = b i := by
      rw [← add_mul, hαβ, one_mul]
    linarith

/-- The common face is the intersection of the original polytope with the
affine translate `u + commonDirection`. -/
theorem mem_commonFace_iff_sub_mem_commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d)) :
    y ∈ HirschCommonFace.commonFace a b u x ↔
      y ∈ Hpoly a b ∧ y - u ∈ HirschCommonFace.commonDirection a b u x := by
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [HirschCommonFace.commonDirection, LinearMap.mem_ker]
    funext ii
    have hiC : ii.1 ∈ HirschCommonFace.commonSourceRows a b u x := ii.2
    have hyi : ⟪a ii.1, y⟫ = b ii.1 := hy.2 ii.1 hiC
    have hui : ⟪a ii.1, u⟫ = b ii.1 :=
      (Finset.mem_filter.1 hiC).2.2.1
    change ⟪a ii.1, y - u⟫ = 0
    rw [inner_sub_right, hyi, hui]
    ring
  · rintro ⟨hyP, hdir⟩
    refine ⟨hyP, ?_⟩
    intro i hiC
    have hker : HirschCommonFace.rowEvalMap a
        (HirschCommonFace.commonSourceRows a b u x) (y - u) = 0 :=
      LinearMap.mem_ker.1 hdir
    have hcoord : ⟪a i, y - u⟫ = 0 := by
      change (HirschCommonFace.rowEvalMap a
          (HirschCommonFace.commonSourceRows a b u x) (y - u)) ⟨i, hiC⟩ = 0
      exact congrFun hker ⟨i, hiC⟩
    have hui : ⟪a i, u⟫ = b i :=
      (Finset.mem_filter.1 hiC).2.2.1
    rw [inner_sub_right, hui] at hcoord
    linarith

/-- A maximal row-circuit augmentation leaving a vertex is already a graph
edge once its common-tight-row carrier lies in the affine line of the
augmentation. -/
theorem rowCircuitStep_adj_of_commonFace_line
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hline : ∀ z, z ∈ HirschCommonFace.commonFace a b x y →
      ∃ t : ℝ, z = x + t • (y - x)) :
    Adj (Hpoly a b) x y := by
  have hxy : x ≠ y := by
    intro h
    apply hstep.2.2.1.1
    rw [h]
    simp
  have hfaceEq : HirschCommonFace.commonFace a b x y = segment ℝ x y := by
    apply Set.Subset.antisymm
    · intro z hz
      have hzP : z ∈ Hpoly a b := hz.1
      obtain ⟨t, hzt⟩ := hline z hz
      have ht1 : t ≤ 1 := by
        by_contra ht
        have ht' : 1 < t := lt_of_not_ge ht
        exact hstep.2.2.2 t ht' (hzt ▸ hzP)
      have ht0 : 0 ≤ t := by
        by_contra ht
        have htneg : t < 0 := lt_of_not_ge ht
        let α : ℝ := 1 / (1 - t)
        let β : ℝ := -t / (1 - t)
        have hden : 0 < 1 - t := by linarith
        have hα : 0 < α := by
          dsimp [α]
          positivity
        have hβ : 0 < β := by
          dsimp [β]
          exact div_pos (neg_pos.mpr htneg) hden
        have hsum : α + β = 1 := by
          dsimp [α, β]
          field_simp [ne_of_gt hden]
          ring
        have hcoef : α * t + β = 0 := by
          dsimp [α, β]
          field_simp [ne_of_gt hden]
          ring
        have hxcoef : α - α * t = 1 := by
          linarith only [hsum, hcoef]
        have hopen : x ∈ openSegment ℝ z y := by
          refine ⟨α, β, hα, hβ, hsum, ?_⟩
          rw [hzt]
          calc
            α • (x + t • (y - x)) + β • y =
                (α - α * t) • x + (α * t + β) • y := by module
            _ = x := by rw [hxcoef, hcoef]; simp
        have hzx : z = x := hx.2 hzP hstep.2.1 hopen
        have hsame : x = x + t • (y - x) := hzx.symm.trans hzt
        have hsmul : t • (y - x) = 0 := by
          have h := congrArg (fun w => w - x) hsame
          have hzero :
              (0 : EuclideanSpace ℝ (Fin d)) = t • (y - x) := by
            calc
              0 = x - x := by simp
              _ = (x + t • (y - x)) - x := h
              _ = t • (y - x) := by abel
          exact hzero.symm
        have htne : t ≠ 0 := ne_of_lt htneg
        have hyx0 : y - x = 0 := by
          calc
            y - x = t⁻¹ • (t • (y - x)) := by
              rw [smul_smul, inv_mul_cancel₀ htne, one_smul]
            _ = 0 := by rw [hsmul, smul_zero]
        exact hxy (sub_eq_zero.mp hyx0).symm
      refine ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, ?_⟩
      rw [hzt]
      module
    · intro z hz
      obtain ⟨α, β, hα, hβ, hsum, hcomb⟩ := hz
      rw [← hcomb]
      refine ⟨?_, ?_⟩
      · intro i
        have hxi := hstep.1 i
        have hyi := hstep.2.1 i
        simp only [inner_add_right, inner_smul_right]
        calc
          α * ⟪a i, x⟫ + β * ⟪a i, y⟫ ≤ α * b i + β * b i :=
            add_le_add (mul_le_mul_of_nonneg_left hxi hα)
              (mul_le_mul_of_nonneg_left hyi hβ)
          _ = (α + β) * b i := by ring
          _ = b i := by rw [hsum, one_mul]
      · intro i hi
        have hix : ⟪a i, x⟫ = b i := (Finset.mem_filter.1 hi).2.2.1
        have hiy : ⟪a i, y⟫ = b i := (Finset.mem_filter.1 hi).2.2.2
        simp only [inner_add_right, inner_smul_right]
        calc
          α * ⟪a i, x⟫ + β * ⟪a i, y⟫ = α * b i + β * b i := by rw [hix, hiy]
          _ = (α + β) * b i := by ring
          _ = b i := by rw [hsum, one_mul]
  have hface : IsExtreme ℝ (Hpoly a b) (segment ℝ x y) := by
    rw [← hfaceEq]
    exact commonFace_isExtreme a b x y
  exact ⟨hxy, hface⟩

/-- If the common-tight-row direction space of two distinct points has
finrank at most one, then every point of their common face lies on their
ambient affine line. -/
theorem commonFace_line_of_dim_le_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hne : y - x ≠ 0)
    (hdim : HirschCommonFace.commonFaceDim a b x y ≤ 1) :
    ∀ z, z ∈ HirschCommonFace.commonFace a b x y →
      ∃ t : ℝ, z = x + t • (y - x) := by
  let W := HirschCommonFace.commonDirection a b x y
  have hgmem : y - x ∈ W := by
    change HirschCommonFace.rowEvalMap a
      (HirschCommonFace.commonSourceRows a b x y) (y - x) = 0
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, y - x⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1]
    ring
  let gW : W := ⟨y - x, hgmem⟩
  have hgWne : gW ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg (fun w : W => (w : EuclideanSpace ℝ (Fin d))) h
    simpa [gW] using h'
  have hdimW : Module.finrank ℝ W ≤ 1 := by
    simpa [HirschCommonFace.commonFaceDim, W] using hdim
  obtain ⟨v0, hgen⟩ := (finrank_le_one_iff).1 hdimW
  obtain ⟨c, hcg⟩ := hgen gW
  have hc : c ≠ 0 := by
    intro hc0
    apply hgWne
    rw [← hcg, hc0, zero_smul]
  intro z hz
  have hzdir : z - x ∈ W :=
    ((mem_commonFace_iff_sub_mem_commonDirection a b x y z).1 hz).2
  let zW : W := ⟨z - x, hzdir⟩
  obtain ⟨k, hkz⟩ := hgen zW
  have hscalar : (k / c) • gW = zW := by
    rw [← hcg, smul_smul, div_mul_cancel₀ k hc, hkz]
  have hval := congrArg (fun w : W => (w : EuclideanSpace ℝ (Fin d))) hscalar
  have hsub : z - x = (k / c) • (y - x) := by
    simpa [zW, gW] using hval.symm
  refine ⟨k / c, ?_⟩
  calc
    z = x + (z - x) := by abel
    _ = x + (k / c) • (y - x) := by rw [hsub]

/-- A maximal row-circuit augmentation from a vertex is an ordinary graph
edge whenever its common face has dimension at most one. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y)
    (hdim : HirschCommonFace.commonFaceDim a b x y ≤ 1) :
    Adj (Hpoly a b) x y := by
  apply rowCircuitStep_adj_of_commonFace_line a b x y hx hstep
  exact commonFace_line_of_dim_le_one a b x y hstep.2.2.1.1 hdim

#print axioms solution
