-- Prove2me | solution 1 for Hirsch.ridge_visible_of_n_le_two_d
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T15:40:22.936692+00:00
-- url     : https://prove2.me/submissions/86e23059-28ba-4981-b866-ddaf82a7f278

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
        have hhalf : ε * C ≤ δ / 2 := hεC
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

theorem tight_sets_eq_of_same_filter
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hT : ∀ i : Fin n, ⟪a i, z₁⟫ = b i ↔ ⟪a i, z₂⟫ = b i) :
    z₁ = z₂ := by
  have hy : ∀ i, ⟪a i, z₁⟫ = b i → ⟪a i, z₂ - z₁⟫ = 0 := by
    intro i ht
    have ht₂ : ⟪a i, z₂⟫ = b i := (hT i).1 ht
    simp [inner_sub_right, ht, ht₂]
  have hdiff : z₂ - z₁ = 0 := extreme_tight_orthogonal hz₁ hy
  exact (sub_eq_zero.1 hdiff).symm

theorem union_card_ge_d_add_one
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hz₂ : z₂ ∈ extremePoints ℝ (Hpoly a b))
    (hne : z₁ ≠ z₂) :
    d + 1 ≤
      ((Finset.univ.filter (fun j : Fin n => ⟪a j, z₁⟫ = b j)) ∪
        Finset.univ.filter (fun j : Fin n => ⟪a j, z₂⟫ = b j)).card := by
  classical
  let t₁ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₁⟫ = b j)
  let t₂ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₂⟫ = b j)
  have h1 : d ≤ t₁.card := tight_card_ge_d hz₁
  have h2 : d ≤ t₂.card := tight_card_ge_d hz₂
  have hTne : t₁ ≠ t₂ := by
    intro hEq
    have hiff : ∀ j : Fin n, ⟪a j, z₁⟫ = b j ↔ ⟪a j, z₂⟫ = b j := by
      intro j
      constructor
      · intro hj
        have hj1 : j ∈ t₁ := Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩
        have hj2 : j ∈ t₂ := hEq ▸ hj1
        exact (Finset.mem_filter.1 hj2).2
      · intro hj
        have hj2 : j ∈ t₂ := Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩
        have hj1 : j ∈ t₁ := hEq.symm ▸ hj2
        exact (Finset.mem_filter.1 hj1).2
    exact hne (tight_sets_eq_of_same_filter hz₁ hiff)
  by_cases h12 : t₁ ⊆ t₂
  · have hss : t₁ ⊂ t₂ := Finset.ssubset_iff_subset_ne.2 ⟨h12, hTne⟩
    have hEq : t₁ ∪ t₂ = t₂ := Finset.union_eq_right.2 h12
    have hlt : t₁.card < t₂.card := Finset.card_lt_card hss
    have : d + 1 ≤ t₂.card := by linarith [Nat.succ_le_of_lt hlt]
    simpa [t₁, t₂, hEq]
  · have hss : t₂ ⊂ t₁ ∪ t₂ := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_union_right, ?_⟩
      intro h
      have : t₁ ⊆ t₂ := by
        intro x hx
        have hx' : x ∈ t₁ ∪ t₂ := Finset.mem_union.2 (Or.inl hx)
        exact h ▸ hx'
      exact h12 this
    have hlt : t₂.card < (t₁ ∪ t₂).card := Finset.card_lt_card hss
    have : d + 1 ≤ (t₁ ∪ t₂).card := by linarith [Nat.succ_le_of_lt hlt]
    simpa [t₁, t₂]

theorem solution
    {d n : ℕ} (hn : n ≤ 2 * d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n)
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hz₂ : z₂ ∈ extremePoints ℝ (Hpoly a b))
    (hne : z₁ ≠ z₂)
    (hzi₁ : ⟪a i, z₁⟫ = b i)
    (hzi₂ : ⟪a i, z₂⟫ = b i)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    ⟪a i, u⟫ = b i ∨
      ∃ r : Fin n, r ≠ i ∧ ⟪a r, u⟫ = b r ∧
        ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r := by
  classical
  by_cases hui : ⟪a i, u⟫ = b i
  · exact Or.inl hui
  · refine Or.inr ?_
    let tU : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, u⟫ = b j)
    let t₁ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₁⟫ = b j)
    let t₂ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₂⟫ = b j)
    have hU : d ≤ tU.card := tight_card_ge_d hu
    have h12 : d + 1 ≤ (t₁ ∪ t₂).card :=
      union_card_ge_d_add_one hz₁ hz₂ hne
    by_contra hnone
    have hdisj : Disjoint tU (t₁ ∪ t₂) := by
      refine Finset.disjoint_left.2 ?_
      intro r hrU hrN
      have hru : ⟪a r, u⟫ = b r := (Finset.mem_filter.1 hrU).2
      have hrne : r ≠ i := by
        intro hri
        subst hri
        exact hui hru
      have hx : ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r := by
        rcases Finset.mem_union.1 hrN with hrt1 | hrt2
        · exact ⟨z₁, extremePoints_subset hz₁, hzi₁, (Finset.mem_filter.1 hrt1).2⟩
        · exact ⟨z₂, extremePoints_subset hz₂, hzi₂, (Finset.mem_filter.1 hrt2).2⟩
      exact hnone ⟨r, hrne, hru, hx⟩
    have hunion : (tU ∪ (t₁ ∪ t₂)).card ≤ n := by
      simpa [Fintype.card_fin] using (tU ∪ (t₁ ∪ t₂)).card_le_univ
    have hinter : tU ∩ (t₁ ∪ t₂) = ∅ := Finset.disjoint_iff_inter_eq_empty.1 hdisj
    have hsum := Finset.card_union_add_card_inter tU (t₁ ∪ t₂)
    have hsum' : (tU ∪ (t₁ ∪ t₂)).card = tU.card + (t₁ ∪ t₂).card := by
      simpa [hinter] using hsum
    have hle : tU.card + (t₁ ∪ t₂).card ≤ n := hsum'.symm.trans_le hunion
    linarith
