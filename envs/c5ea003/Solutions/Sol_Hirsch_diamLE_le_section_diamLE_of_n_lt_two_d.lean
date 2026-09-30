-- Prove2me | solution 1 for Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:54:58.688534+00:00
-- url     : https://prove2.me/submissions/19dcd669-189e-4b8c-8a39-d194439f3048

import Definitions.Def_Hirsch_model
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped RealInnerProductSpace
open Set Module Hirsch

noncomputable section

variable {d n : ℕ}

theorem extreme_tight_orthogonal
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hy : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  by_contra hy0
  have hxP : x ∈ Hpoly a b := hx.1
  let S : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ ≠ b i)
  by_cases hS : S = ∅
  · have hyi : ∀ i, ⟪a i, y⟫ = 0 := by
      intro i
      apply hy
      by_contra hne
      have hi : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
      rw [hS] at hi
      exact Finset.notMem_empty i hi
    have hp1 : x + y ∈ Hpoly a b := by
      intro i
      simpa [inner_add_right, hyi i] using hxP i
    have hp2 : x - y ∈ Hpoly a b := by
      intro i
      simpa [inner_sub_right, hyi i] using hxP i
    have hop : x ∈ openSegment ℝ (x - y) (x + y) := mem_openSegment_sub_add x y
    have heq : x - y = x := hx.2 hp2 hp1 hop
    have : (x - y) + y = x + y := by rw [heq]
    have hyz : y = 0 := by simpa using this
    exact hy0 hyz
  · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    let δ : ℝ := S.inf' hSne (fun i => b i - ⟪a i, x⟫)
    have hδ : 0 < δ := by
      obtain ⟨iδ, hiδ, hδeq⟩ := S.exists_mem_eq_inf' hSne (fun i => b i - ⟪a i, x⟫)
      have hne : ⟪a iδ, x⟫ ≠ b iδ := (Finset.mem_filter.1 hiδ).2
      have : 0 < b iδ - ⟪a iδ, x⟫ := sub_pos.2 (lt_of_le_of_ne (hxP iδ) hne)
      simpa [δ, hδeq] using this
    let C : ℝ := ∑ i, |⟪a i, y⟫|
    have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
    let ε : ℝ := δ / (2 * (C + 1))
    have hεpos : 0 < ε := div_pos hδ (by positivity)
    have hεC : ε * C ≤ δ / 2 := by
      have hle : C ≤ C + 1 := by linarith
      have : ε * C ≤ ε * (C + 1) := mul_le_mul_of_nonneg_left hle hεpos.le
      have hden : (2 * (C + 1) : ℝ) ≠ 0 := by positivity
      have : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp [hden]
      linarith
    have hmem (σ : ℝ) (hσabs : |σ| = ε) : x + σ • y ∈ Hpoly a b := by
      intro i
      have hinner : ⟪a i, x + σ • y⟫ = ⟪a i, x⟫ + σ * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hinner]
      by_cases ht : ⟪a i, x⟫ = b i
      · have : ⟪a i, y⟫ = 0 := hy i ht
        simp [ht, this]
      · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
        have hslack : δ ≤ b i - ⟪a i, x⟫ := Finset.inf'_le _ hiS
        have habs : |σ * ⟪a i, y⟫| ≤ ε * C := by
          have h1 : |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by simp [abs_mul, hσabs]
          have h2 : |⟪a i, y⟫| ≤ C :=
            Finset.single_le_sum (f := fun j : Fin n => |⟪a j, y⟫|)
              (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
          calc
            |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := h1
            _ ≤ ε * C := mul_le_mul_of_nonneg_left h2 hεpos.le
        have : σ * ⟪a i, y⟫ ≤ |σ * ⟪a i, y⟫| := le_abs_self _
        linarith
    have hp1 : x + ε • y ∈ Hpoly a b := hmem ε (abs_of_pos hεpos)
    have hp2 : x - ε • y ∈ Hpoly a b := by
      simpa [sub_eq_add_neg, neg_smul] using hmem (-ε) (by simp [abs_of_pos hεpos])
    have hop : x ∈ openSegment ℝ (x - ε • y) (x + ε • y) :=
      mem_openSegment_sub_add x (ε • y)
    have heq : x - ε • y = x := hx.2 hp2 hp1 hop
    have hyε : ε • y = 0 := by
      have : (x - ε • y) + ε • y = x + ε • y := by rw [heq]
      simpa using this
    exact hy0 ((smul_eq_zero.1 hyε).resolve_left hεpos.ne')

theorem tight_card_ge_d
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ (Finset.univ.filter (fun i : Fin n => ⟪a i, x⟫ = b i)).card := by
  classical
  let sU : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (sU → ℝ) :=
    LinearMap.pi fun i : sU => innerSL ℝ (a i.1)
  by_cases hbot : f.ker = ⊥
  · have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      exact hbot
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdE : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (sU → ℝ) = sU.card := by
      simp [Fintype.card_coe]
    simpa [hdE, hcod] using hle
  · obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hyi : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0 := by
      intro i ht
      have hi : i ∈ sU := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
      have hf0 : f y = 0 := LinearMap.mem_ker.1 hyker
      have : f y ⟨i, hi⟩ = 0 := by simp [hf0]
      simpa [f, innerSL] using this
    exact (hy0 (extreme_tight_orthogonal hx hyi)).elim

theorem share_tight_row_of_n_lt_two_d (hn : n < 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ i : Fin n, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  classical
  let sU : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, u⟫ = b i)
  let sV : Finset (Fin n) := Finset.univ.filter (fun i => ⟪a i, v⟫ = b i)
  have hU : d ≤ sU.card := tight_card_ge_d hu
  have hV : d ≤ sV.card := tight_card_ge_d hv
  have hunion : (sU ∪ sV).card ≤ n := by
    simpa [Fintype.card_fin] using (sU ∪ sV).card_le_univ
  by_contra hnone
  have hdisj : Disjoint sU sV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    exact hnone ⟨i, (Finset.mem_filter.1 hiU).2, (Finset.mem_filter.1 hiV).2⟩
  have hinter : sU ∩ sV = ∅ := Finset.disjoint_iff_inter_eq_empty.1 hdisj
  have hsum := Finset.card_union_add_card_inter sU sV
  have hsum' : (sU ∪ sV).card = sU.card + sV.card := by
    simpa [hinter] using hsum
  have : sU.card + sV.card ≤ n := hsum'.symm.trans_le hunion
  linarith

theorem equality_section_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}) := by
  refine ⟨fun x hx => hx.1, ?_⟩
  intro p hp q hq z hz hzopen
  refine ⟨hp, ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
  have hzi : ⟪a i, z⟫ = b i := hz.2
  have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
    rw [← hzcomb]
    simp [inner_add_right, inner_smul_right]
  have hp_le := hp i
  have hq_le := hq i
  by_contra hpne
  have hplt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hpne
  have h1 : α * ⟪a i, p⟫ < α * b i := mul_lt_mul_of_pos_left hplt hα
  have h2 : β * ⟪a i, q⟫ ≤ β * b i := mul_le_mul_of_nonneg_left hq_le hβ.le
  have hb : α * b i + β * b i = b i := by rw [← add_mul, hαβ, one_mul]
  linarith

theorem adj_of_extreme_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P F : Set E} {u v : E}
    (hF : IsExtreme ℝ P F) (h : Adj F u v) : Adj P u v :=
  ⟨h.1, hF.trans h.2⟩

theorem solution {d n B : ℕ} (hn : n < 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hF : ∀ i : Fin n, DiamLE (Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}) B) :
    DiamLE (Hpoly a b) B := by
  intro u hu v hv
  obtain ⟨i, hiu, hiv⟩ := share_tight_row_of_n_lt_two_d hn a b hu hv
  let F := Hpoly a b ∩ {x | ⟪a i, x⟫ = b i}
  have hFext : IsExtreme ℝ (Hpoly a b) F := equality_section_isExtreme a b i
  have huF : u ∈ extremePoints ℝ F := by
    have heq := hFext.extremePoints_eq
    have huFmem : u ∈ F := ⟨extremePoints_subset hu, hiu⟩
    exact heq.symm ▸ ⟨huFmem, hu⟩
  have hvF : v ∈ extremePoints ℝ F := by
    have heq := hFext.extremePoints_eq
    have hvFmem : v ∈ F := ⟨extremePoints_subset hv, hiv⟩
    exact heq.symm ▸ ⟨hvFmem, hv⟩
  obtain ⟨w, hw0, hwB, hs⟩ := hF i u huF v hvF
  refine ⟨w, hw0, hwB, ?_⟩
  intro j hj
  rcases hs j hj with hstay | hadj
  · exact Or.inl hstay
  · exact Or.inr (adj_of_extreme_face hFext hadj)
