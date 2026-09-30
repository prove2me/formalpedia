-- Prove2me | solution 1 for Hirsch.ridge_visible_neighbor_of_n_eq_two_d_add_two
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T17:16:22.067986+00:00
-- url     : https://prove2.me/submissions/b80f810a-475b-41b8-8390-39183e3710f5

import Definitions.Def_Hirsch_model
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped RealInnerProductSpace
open Set Module Hirsch Bornology

noncomputable section

variable {d n : ℕ}

/-! Tight-row spanning, copied from the n ≤ 2d ridge-visible lemma. -/

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

def IsRidgeVisible
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) (u : EuclideanSpace ℝ (Fin d)) : Prop :=
  ⟪a i, u⟫ = b i ∨
    ∃ r : Fin n, r ≠ i ∧ ⟪a r, u⟫ = b r ∧
      ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r

theorem already_rv_of_n_le_two_d
    (hn : n ≤ 2 * d)
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
    IsRidgeVisible a b i u := by
  classical
  by_cases hui : ⟪a i, u⟫ = b i
  · exact Or.inl hui
  · refine Or.inr ?_
    let tU : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, u⟫ = b j)
    let t₁ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₁⟫ = b j)
    let t₂ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₂⟫ = b j)
    have hU : d ≤ tU.card := tight_card_ge_d hu
    have h12 : d + 1 ≤ (t₁ ∪ t₂).card := union_card_ge_d_add_one hz₁ hz₂ hne
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

/-! Dual basis at a simple vertex. -/

def tightEval (a : Fin n → EuclideanSpace ℝ (Fin d)) (tU : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (tU → ℝ) :=
  LinearMap.pi fun j : tU => innerSL ℝ (a j.1)

theorem tightEval_injective
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    Function.Injective
      (tightEval a (Finset.univ.filter (fun j : Fin n => ⟪a j, u⟫ = b j))) := by
  let tU : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, u⟫ = b j)
  let f := tightEval a tU
  intro y₁ y₂ hyeq
  have hsub : f (y₁ - y₂) = 0 := by
    rw [map_sub, hyeq, sub_self]
  have hyi : ∀ i, ⟪a i, u⟫ = b i → ⟪a i, y₁ - y₂⟫ = 0 := by
    intro i ht
    have hi : i ∈ tU := Finset.mem_filter.2 ⟨Finset.mem_univ i, ht⟩
    have hval : f (y₁ - y₂) ⟨i, hi⟩ = ⟪a i, y₁ - y₂⟫ := rfl
    have h0 : f (y₁ - y₂) ⟨i, hi⟩ = 0 := congrFun hsub ⟨i, hi⟩
    exact hval.symm.trans h0
  exact sub_eq_zero.1 (extreme_tight_orthogonal hu hyi)

theorem leave_one_dir
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hsimple : (Finset.univ.filter (fun j : Fin n => ⟪a j, u⟫ = b j)).card = d)
    (L : Fin n) (hL : ⟪a L, u⟫ = b L) :
    ∃ y : EuclideanSpace ℝ (Fin d),
      ⟪a L, y⟫ = -1 ∧
      (∀ j : Fin n, ⟪a j, u⟫ = b j → j ≠ L → ⟪a j, y⟫ = 0) ∧
      y ≠ 0 := by
  classical
  let tU : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, u⟫ = b j)
  have hLmem : L ∈ tU := Finset.mem_filter.2 ⟨Finset.mem_univ L, hL⟩
  let f := tightEval a tU
  have hinj : Function.Injective f := tightEval_injective hu
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = Module.finrank ℝ (tU → ℝ) := by
    have hdE : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (tU → ℝ) = tU.card := by simp [Fintype.card_coe]
    rw [hdE, hcod, hsimple]
  let e : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (tU → ℝ) :=
    LinearMap.linearEquivOfInjective f hinj hdim
  let target : tU → ℝ := fun j => if j.1 = L then (-1 : ℝ) else 0
  let y : EuclideanSpace ℝ (Fin d) := e.symm target
  have hf : f y = target := by
    have hsy : e y = target := by
      dsimp [y]
      exact e.apply_symm_apply target
    have heq : e y = f y :=
      LinearMap.linearEquivOfInjective_apply (f := f) hinj hdim y
    exact heq.symm.trans hsy
  refine ⟨y, ?_, ?_, ?_⟩
  · have hval : f y ⟨L, hLmem⟩ = ⟪a L, y⟫ := rfl
    have htar : target ⟨L, hLmem⟩ = (-1 : ℝ) := if_pos rfl
    have : f y ⟨L, hLmem⟩ = target ⟨L, hLmem⟩ := by rw [hf]
    exact hval.symm.trans (this.trans htar)
  · intro j hjt hjne
    have hjmem : j ∈ tU := Finset.mem_filter.2 ⟨Finset.mem_univ j, hjt⟩
    have hval : f y ⟨j, hjmem⟩ = ⟪a j, y⟫ := rfl
    have htar : target ⟨j, hjmem⟩ = 0 := if_neg hjne
    have : f y ⟨j, hjmem⟩ = target ⟨j, hjmem⟩ := by rw [hf]
    exact hval.symm.trans (this.trans htar)
  · intro hy0
    have hf0 : f y = 0 := by rw [hy0, map_zero]
    have htar0 : target = 0 := hf.symm.trans hf0
    have : target ⟨L, hLmem⟩ = 0 := congrFun htar0 ⟨L, hLmem⟩
    have htar : target ⟨L, hLmem⟩ = (-1 : ℝ) := if_pos rfl
    have hneg : (-1 : ℝ) = 0 := htar.symm.trans this
    exact (one_ne_zero : (1 : ℝ) ≠ 0) (neg_eq_zero.mp hneg)

theorem ray_unbounded
    (u y : EuclideanSpace ℝ (Fin d)) (hy : y ≠ 0) :
    ¬ IsBounded (Set.range fun k : ℕ => u + (k : ℝ) • y) := by
  intro hbd
  obtain ⟨R, hR⟩ := hbd.subset_closedBall u
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  let k : ℕ := Nat.ceil (R / ‖y‖ + 1)
  have hk : R < (k : ℝ) * ‖y‖ := by
    have : R / ‖y‖ < k := by
      have hle : R / ‖y‖ ≤ Nat.ceil (R / ‖y‖ + 1) := by
        have : R / ‖y‖ ≤ R / ‖y‖ + 1 := by linarith
        exact this.trans (Nat.le_ceil _)
      have : (k : ℝ) = Nat.ceil (R / ‖y‖ + 1) := rfl
      have hstrict : R / ‖y‖ < R / ‖y‖ + 1 := by linarith
      have : (R / ‖y‖ + 1) ≤ k := Nat.le_ceil _
      linarith
    exact (div_lt_iff₀ hypos).1 this
  have hmem : u + (k : ℝ) • y ∈ Metric.closedBall u R :=
    hR ⟨k, rfl⟩
  have hdist : dist (u + (k : ℝ) • y) u = (k : ℝ) * ‖y‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (n := k))]
  have : (k : ℝ) * ‖y‖ ≤ R := by
    simpa [Metric.mem_closedBall, hdist] using hmem
  linarith

theorem equality_face_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (S : Finset (Fin n)) :
    IsExtreme ℝ (Hpoly a b)
      {p | p ∈ Hpoly a b ∧ ∀ j ∈ S, ⟪a j, p⟫ = b j} := by
  refine ⟨fun p hp => hp.1, ?_⟩
  intro p hp q hq z hz hzopen
  refine ⟨hp, ?_⟩
  intro j hjS
  have hzt : ⟪a j, z⟫ = b j := hz.2 j hjS
  obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
  have hinner : ⟪a j, z⟫ = α * ⟪a j, p⟫ + β * ⟪a j, q⟫ := by
    rw [← hzcomb]
    simp [inner_add_right, inner_smul_right]
  have hp_le := hp j
  have hq_le := hq j
  by_contra hpne
  have hplt : ⟪a j, p⟫ < b j := lt_of_le_of_ne hp_le hpne
  have h1 : α * ⟪a j, p⟫ < α * b j := mul_lt_mul_of_pos_left hplt hα
  have h2 : β * ⟪a j, q⟫ ≤ β * b j := mul_le_mul_of_nonneg_left hq_le hβ.le
  have hb : α * b j + β * b j = b j := by rw [← add_mul, hαβ, one_mul]
  linarith

lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg]
    simpa only [neg_smul] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

/-- From a simple vertex, leaving one tight row along its extreme ray hits a
new inequality at an adjacent vertex. -/
theorem simple_leave_one_neighbor
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (hbd : IsBounded (Hpoly a b))
    {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hsimple : (Finset.univ.filter (fun j : Fin n => ⟪a j, u⟫ = b j)).card = d)
    (L : Fin n) (hL : ⟪a L, u⟫ = b L) :
    ∃ w E,
      w ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (Hpoly a b) u w ∧
      ⟪a E, u⟫ ≠ b E ∧
      ⟪a E, w⟫ = b E ∧
      (∀ j : Fin n, ⟪a j, u⟫ = b j → j ≠ L → ⟪a j, w⟫ = b j) := by
  classical
  obtain ⟨y, hyL, hyorth, hy0⟩ := leave_one_dir hu hsimple L hL
  let hit : Finset (Fin n) := Finset.univ.filter (fun k => 0 < ⟪a k, y⟫)
  have hhit : hit.Nonempty := by
    by_contra hempty
    have hno : ∀ k, ¬ 0 < ⟪a k, y⟫ := by
      intro k hk
      have hkmem : k ∈ hit := Finset.mem_filter.2 ⟨Finset.mem_univ k, hk⟩
      have hempty' : hit = ∅ := Finset.not_nonempty_iff_eq_empty.1 hempty
      rw [hempty'] at hkmem
      exact Finset.notMem_empty k hkmem
    have hray : ∀ k : ℕ, u + (k : ℝ) • y ∈ Hpoly a b := by
      intro k i
      have : ⟪a i, u + (k : ℝ) • y⟫ = ⟪a i, u⟫ + (k : ℝ) * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [this]
      have hiP := hu.1 i
      by_cases hpos : 0 < ⟪a i, y⟫
      · exact (hno i hpos).elim
      · have hyi : ⟪a i, y⟫ ≤ 0 := le_of_not_gt hpos
        have : (k : ℝ) * ⟪a i, y⟫ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hyi
        linarith
    have hsub : Set.range (fun k : ℕ => u + (k : ℝ) • y) ⊆ Hpoly a b := by
      intro x hx
      obtain ⟨k, rfl⟩ := hx
      exact hray k
    exact (ray_unbounded u y hy0) (hbd.subset hsub)
  let tstar : ℝ := hit.inf' hhit (fun k => (b k - ⟪a k, u⟫) / ⟪a k, y⟫)
  have htpos : 0 < tstar := by
    obtain ⟨k, hkhit, hkeq⟩ := hit.exists_mem_eq_inf' hhit
      (fun k => (b k - ⟪a k, u⟫) / ⟪a k, y⟫)
    have hky : 0 < ⟪a k, y⟫ := (Finset.mem_filter.1 hkhit).2
    have hslack : ⟪a k, u⟫ < b k := by
      by_contra hge
      have hle : b k ≤ ⟪a k, u⟫ := le_of_not_gt hge
      have heq : ⟪a k, u⟫ = b k := le_antisymm (hu.1 k) hle
      have : k = L ∨ k ≠ L := em _
      -- tight rows cannot have positive directional derivative
      have hky0 : ⟪a k, y⟫ ≤ 0 := by
        by_cases hkL : k = L
        · subst hkL
          simpa [hyL] using (by linarith : (-1 : ℝ) ≤ 0)
        · have : ⟪a k, y⟫ = 0 := hyorth k heq hkL
          linarith
      linarith
    have hratio : 0 < (b k - ⟪a k, u⟫) / ⟪a k, y⟫ :=
      div_pos (sub_pos.2 hslack) hky
    simpa [tstar, hkeq] using hratio
  let w : EuclideanSpace ℝ (Fin d) := u + tstar • y
  have hwP : w ∈ Hpoly a b := by
    intro j
    have : ⟪a j, w⟫ = ⟪a j, u⟫ + tstar * ⟪a j, y⟫ := by
      simp [w, inner_add_right, inner_smul_right]
    rw [this]
    by_cases hpos : 0 < ⟪a j, y⟫
    · have hjhit : j ∈ hit := Finset.mem_filter.2 ⟨Finset.mem_univ j, hpos⟩
      have hle : tstar ≤ (b j - ⟪a j, u⟫) / ⟪a j, y⟫ := Finset.inf'_le _ hjhit
      have hmul : tstar * ⟪a j, y⟫ ≤ b j - ⟪a j, u⟫ := (le_div_iff₀ hpos).mp hle
      linarith [hu.1 j]
    · have hyj : ⟪a j, y⟫ ≤ 0 := le_of_not_gt hpos
      have : tstar * ⟪a j, y⟫ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hyj
      linarith [hu.1 j]
  obtain ⟨E, hEhit, hEeq⟩ := hit.exists_mem_eq_inf' hhit
    (fun k => (b k - ⟪a k, u⟫) / ⟪a k, y⟫)
  have hEy : 0 < ⟪a E, y⟫ := (Finset.mem_filter.1 hEhit).2
  have hEt : tstar = (b E - ⟪a E, u⟫) / ⟪a E, y⟫ := by
    simpa [tstar] using hEeq
  have hEw : ⟪a E, w⟫ = b E := by
    have : ⟪a E, w⟫ = ⟪a E, u⟫ + tstar * ⟪a E, y⟫ := by
      simp [w, inner_add_right, inner_smul_right]
    rw [this, hEt, div_mul_cancel₀ _ hEy.ne']
    ring
  have hEu : ⟪a E, u⟫ ≠ b E := by
    intro heq
    have hEdir : ⟪a E, y⟫ ≤ 0 := by
      by_cases hEL : E = L
      · subst hEL
        simpa [hyL] using (by linarith : (-1 : ℝ) ≤ 0)
      · have : ⟪a E, y⟫ = 0 := hyorth E heq hEL
        linarith
    linarith
  have hwne : u ≠ w := by
    intro h
    have : tstar • y = 0 := by
      have : u + tstar • y = u := by simpa [w] using h.symm
      simpa using this
    rcases smul_eq_zero.1 this with ht0 | hyz
    · exact htpos.ne' ht0
    · exact hy0 hyz
  let S : Finset (Fin n) :=
    (Finset.univ.filter (fun j : Fin n => ⟪a j, u⟫ = b j)).erase L
  let F : Set (EuclideanSpace ℝ (Fin d)) :=
    {p | p ∈ Hpoly a b ∧ ∀ j ∈ S, ⟪a j, p⟫ = b j}
  have hFext : IsExtreme ℝ (Hpoly a b) F := equality_face_isExtreme a b S
  have huF : u ∈ F := by
    refine ⟨hu.1, ?_⟩
    intro j hjS
    have hjU : j ∈ Finset.univ.filter (fun j : Fin n => ⟪a j, u⟫ = b j) :=
      (Finset.mem_erase.1 hjS).2
    exact (Finset.mem_filter.1 hjU).2
  have hwF : w ∈ F := by
    refine ⟨hwP, ?_⟩
    intro j hjS
    have hjne : j ≠ L := (Finset.mem_erase.1 hjS).1
    have hjt : ⟪a j, u⟫ = b j :=
      (Finset.mem_filter.1 (Finset.mem_erase.1 hjS).2).2
    have : ⟪a j, w⟫ = ⟪a j, u⟫ + tstar * ⟪a j, y⟫ := by
      simp [w, inner_add_right, inner_smul_right]
    rw [this, hyorth j hjt hjne, mul_zero, add_zero, hjt]
  have hFconv : Convex ℝ F := by
    intro x hx y hy α β hα hβ hαβ
    refine ⟨?_, ?_⟩
    · intro i
      have hxle := hx.1 i
      have hyle := hy.1 i
      have hsum : ⟪a i, α • x + β • y⟫ = α * ⟪a i, x⟫ + β * ⟪a i, y⟫ := by
        simp [inner_add_right, inner_smul_right]
      rw [hsum]
      have h1 : α * ⟪a i, x⟫ ≤ α * b i := mul_le_mul_of_nonneg_left hxle hα
      have h2 : β * ⟪a i, y⟫ ≤ β * b i := mul_le_mul_of_nonneg_left hyle hβ
      have h3 : α * b i + β * b i = b i := by rw [← add_mul, hαβ, one_mul]
      linarith
    · intro j hjS
      have hxj := hx.2 j hjS
      have hyj := hy.2 j hjS
      have : ⟪a j, α • x + β • y⟫ = α * b j + β * b j := by
        simp [inner_add_right, inner_smul_right, hxj, hyj]
      have : ⟪a j, α • x + β • y⟫ = b j := by
        rw [this, ← add_mul, hαβ, one_mul]
      exact this
  have hsegF : segment ℝ u w ⊆ F := hFconv.segment_subset huF hwF
  have hFseg : F ⊆ segment ℝ u w := by
    intro p hp
    have hpker : ∀ j, ⟪a j, u⟫ = b j → j ≠ L → ⟪a j, p - u⟫ = 0 := by
      intro j hjt hjne
      have hjS : j ∈ S :=
        Finset.mem_erase.2 ⟨hjne, Finset.mem_filter.2 ⟨Finset.mem_univ j, hjt⟩⟩
      have hpt : ⟪a j, p⟫ = b j := hp.2 j hjS
      rw [inner_sub_right, hpt, hjt, sub_self]
    have hyspan : p - u = (-⟪a L, p - u⟫) • y := by
      have hker : ∀ j, ⟪a j, u⟫ = b j →
          ⟪a j, (p - u) - (-⟪a L, p - u⟫) • y⟫ = 0 := by
        intro j hjt
        by_cases hjL : j = L
        · subst hjL
          rw [inner_sub_right, inner_smul_right, hyL]
          ring
        · have hp0 : ⟪a j, p - u⟫ = 0 := hpker j hjt hjL
          have hyj : ⟪a j, y⟫ = 0 := hyorth j hjt hjL
          rw [inner_sub_right, inner_smul_right, hp0, hyj, mul_zero, sub_zero]
      have hz : (p - u) - (-⟪a L, p - u⟫) • y = 0 :=
        extreme_tight_orthogonal hu hker
      exact eq_of_sub_eq_zero hz
    let t : ℝ := -⟪a L, p - u⟫
    have hpform : p = u + t • y := by
      have : p - u = t • y := by simpa [t] using hyspan
      calc
        p = u + (p - u) := by abel
        _ = u + t • y := by rw [this]
    have ht0 : 0 ≤ t := by
      have hple : ⟪a L, p⟫ ≤ b L := hp.1 L
      have hpeq : ⟪a L, p⟫ = b L + -t := by
        rw [hpform]
        simp [inner_add_right, inner_smul_right, hL, hyL]
      linarith
    have htt : t ≤ tstar := by
      by_contra hgt
      have hlt : tstar < t := lt_of_not_ge hgt
      have hpe : ⟪a E, p⟫ = ⟪a E, u⟫ + t * ⟪a E, y⟫ := by
        rw [hpform]
        simp [inner_add_right, inner_smul_right]
      have hwe : ⟪a E, u⟫ + tstar * ⟪a E, y⟫ = b E := by
        have : ⟪a E, w⟫ = ⟪a E, u⟫ + tstar * ⟪a E, y⟫ := by
          simp [w, inner_add_right, inner_smul_right]
        linarith [hEw]
      have : b E < ⟪a E, p⟫ := by
        rw [hpe]
        nlinarith [hEy, hwe]
      exact (not_le.2 this) (hp.1 E)
    let α : ℝ := t / tstar
    have hα0 : 0 ≤ α := div_nonneg ht0 htpos.le
    have hα1 : α ≤ 1 := (div_le_one htpos).2 htt
    have hαt : α * tstar = t := div_mul_cancel₀ t htpos.ne'
    refine ⟨1 - α, α, by linarith, hα0, by ring, ?_⟩
    have hcalc :
        (1 - α) • u + α • w = u + t • y := by
      change (1 - α) • u + α • (u + tstar • y) = u + t • y
      rw [smul_add, ← add_assoc, ← add_smul, sub_add_cancel, one_smul, smul_smul, hαt]
    rw [hcalc, hpform]
  have hEq : F = segment ℝ u w := subset_antisymm hFseg hsegF
  have hadj : Adj (Hpoly a b) u w := ⟨hwne, hEq ▸ hFext⟩
  have hwex : w ∈ extremePoints ℝ (Hpoly a b) := adj_right_extreme _ hadj
  have hkept : ∀ j : Fin n, ⟪a j, u⟫ = b j → j ≠ L → ⟪a j, w⟫ = b j := by
    intro j hjt hjne
    have hjS : j ∈ S :=
      Finset.mem_erase.2 ⟨hjne, Finset.mem_filter.2 ⟨Finset.mem_univ j, hjt⟩⟩
    exact hwF.2 j hjS
  exact ⟨w, E, hwex, hadj, hEu, hEw, hkept⟩

theorem solution
    {d n : ℕ} (hn : n ≤ 2 * d + 2)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : IsBounded (Hpoly a b))
    (hsimple : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (Finset.univ.filter (fun j : Fin n => ⟪a j, x⟫ = b j)).card = d)
    (i : Fin n)
    {z₁ z₂ : EuclideanSpace ℝ (Fin d)}
    (hz₁ : z₁ ∈ extremePoints ℝ (Hpoly a b))
    (hz₂ : z₂ ∈ extremePoints ℝ (Hpoly a b))
    (hne : z₁ ≠ z₂)
    (hzi₁ : ⟪a i, z₁⟫ = b i)
    (hzi₂ : ⟪a i, z₂⟫ = b i)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    (⟪a i, u⟫ = b i ∨
      ∃ r : Fin n, r ≠ i ∧ ⟪a r, u⟫ = b r ∧
        ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) ∨
    ∃ w, w ∈ extremePoints ℝ (Hpoly a b) ∧ Adj (Hpoly a b) u w ∧
      (⟪a i, w⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, w⟫ = b r ∧
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) := by
  classical
  by_cases huRV : IsRidgeVisible a b i u
  · exact Or.inl huRV
  have hn2 : ¬ n ≤ 2 * d := by
    intro hle
    exact huRV (already_rv_of_n_le_two_d hle a b i hz₁ hz₂ hne hzi₁ hzi₂ u hu)
  have hdpos : 0 < d := by
    by_contra hd
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst hd0
    have : Subsingleton (EuclideanSpace ℝ (Fin 0)) := inferInstance
    exact hne (Subsingleton.elim z₁ z₂)
  let tU : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, u⟫ = b j)
  let t₁ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₁⟫ = b j)
  let t₂ : Finset (Fin n) := Finset.univ.filter (fun j => ⟪a j, z₂⟫ = b j)
  have hUcard : tU.card = d := hsimple u hu
  have h12 : d + 1 ≤ (t₁ ∪ t₂).card := union_card_ge_d_add_one hz₁ hz₂ hne
  have hNear : t₁ ∪ t₂ ⊆ Finset.univ.filter (fun r : Fin n =>
      r = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a r, x⟫ = b r) := by
    intro r hr
    refine Finset.mem_filter.2 ⟨Finset.mem_univ r, ?_⟩
    rcases Finset.mem_union.1 hr with h1 | h2
    · exact Or.inr ⟨z₁, extremePoints_subset hz₁, hzi₁, (Finset.mem_filter.1 h1).2⟩
    · exact Or.inr ⟨z₂, extremePoints_subset hz₂, hzi₂, (Finset.mem_filter.1 h2).2⟩
  have hUfar : ∀ j ∈ tU, ¬ (j = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a j, x⟫ = b j) := by
    intro j hjU hnear
    have hjt : ⟪a j, u⟫ = b j := (Finset.mem_filter.1 hjU).2
    rcases hnear with hij | ⟨x, hxP, hxi, hxj⟩
    · subst hij
      exact huRV (Or.inl hjt)
    · have hrne : j ≠ i := by
        intro hij
        subst hij
        exact huRV (Or.inl hjt)
      exact huRV (Or.inr ⟨j, hrne, hjt, x, hxP, hxi, hxj⟩)
  have hdisj : Disjoint tU (t₁ ∪ t₂) := by
    refine Finset.disjoint_left.2 ?_
    intro j hjU hj12
    have : j = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a j, x⟫ = b j :=
      (Finset.mem_filter.1 (hNear hj12)).2
    exact hUfar j hjU this
  have hUne : tU.Nonempty := by
    have : 0 < tU.card := by rw [hUcard]; exact hdpos
    exact Finset.card_pos.1 this
  have hnb : ∀ L : tU, ∃ w E,
      w ∈ extremePoints ℝ (Hpoly a b) ∧
      Adj (Hpoly a b) u w ∧
      ⟪a E, u⟫ ≠ b E ∧
      ⟪a E, w⟫ = b E ∧
      (∀ j : Fin n, ⟪a j, u⟫ = b j → j ≠ L.1 → ⟪a j, w⟫ = b j) := by
    intro L
    exact simple_leave_one_neighbor hbd hu (hsimple u hu) L.1
      (Finset.mem_filter.1 L.2).2
  choose wfun Efun hwexf hadjf hEuf hEwf hkeptf using hnb
  by_cases hfound : ∃ L : tU, IsRidgeVisible a b i (wfun L)
  · obtain ⟨L, hRV⟩ := hfound
    exact Or.inr ⟨wfun L, hwexf L, hadjf L, hRV⟩
  have hnone : ∀ L : tU, ¬ IsRidgeVisible a b i (wfun L) := by
    intro L hRV
    exact hfound ⟨L, hRV⟩
  have hEfar : ∀ L : tU,
      ¬ (Efun L = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a (Efun L), x⟫ = b (Efun L)) := by
    intro L h
    rcases h with hEi | hx
    · subst hEi
      exact hnone L (Or.inl (hEwf L))
    · have hne' : Efun L ≠ i := by
        intro hEi
        subst hEi
        exact hnone L (Or.inl (hEwf L))
      exact hnone L (Or.inr ⟨Efun L, hne', hEwf L, hx⟩)
  have hEnotU : ∀ L : tU, Efun L ∉ tU := by
    intro L hE
    exact hEuf L (Finset.mem_filter.1 hE).2
  obtain ⟨L0, hL0mem⟩ := hUne
  let L0s : tU := ⟨L0, hL0mem⟩
  let H : Fin n := Efun L0s
  have hHfar : ¬ (H = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a H, x⟫ = b H) :=
    hEfar L0s
  have hHnotU : H ∉ tU := hEnotU L0s
  have hTUHcard : (tU ∪ {H}).card = d + 1 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hHnotU),
      Finset.card_singleton, hUcard]
  have hdisjH : Disjoint (tU ∪ {H}) (t₁ ∪ t₂) := by
    refine Finset.disjoint_left.2 ?_
    intro j hj hj12
    have hnear : j = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a j, x⟫ = b j :=
      (Finset.mem_filter.1 (hNear hj12)).2
    rcases Finset.mem_union.1 hj with hjU | hjH
    · exact hUfar j hjU hnear
    · have : j = H := Finset.mem_singleton.1 hjH
      subst this
      exact hHfar hnear
  have hsumle : (tU ∪ {H}).card + (t₁ ∪ t₂).card ≤ n := by
    have hunion : ((tU ∪ {H}) ∪ (t₁ ∪ t₂)).card ≤ n := by
      simpa [Fintype.card_fin] using ((tU ∪ {H}) ∪ (t₁ ∪ t₂)).card_le_univ
    have hinter : (tU ∪ {H}) ∩ (t₁ ∪ t₂) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.1 hdisjH
    have hsum := Finset.card_union_add_card_inter (tU ∪ {H}) (t₁ ∪ t₂)
    rw [hinter, Finset.card_empty, add_zero] at hsum
    exact hsum.symm.trans_le hunion
  have hnEq : n = 2 * d + 2 := by
    have : d + 1 + (d + 1) ≤ n := by
      have := hsumle
      rw [hTUHcard] at this
      linarith
    linarith
  have h12eq : (t₁ ∪ t₂).card = d + 1 :=
    le_antisymm (by linarith [hTUHcard, hsumle, hnEq]) h12
  have hcov : tU ∪ {H} ∪ (t₁ ∪ t₂) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisjH, hTUHcard, h12eq, Fintype.card_fin, hnEq]
    ring
  have hEH : ∀ L : tU, Efun L = H := by
    intro L
    have hEmem : Efun L ∈ tU ∪ {H} ∪ (t₁ ∪ t₂) := by
      have : Efun L ∈ Finset.univ := Finset.mem_univ _
      rwa [← hcov] at this
    rcases Finset.mem_union.1 hEmem with h1 | h2
    · rcases Finset.mem_union.1 h1 with hU | hHs
      · exact (hEnotU L hU).elim
      · exact Finset.mem_singleton.1 hHs
    · have hnear : Efun L = i ∨
          ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a (Efun L), x⟫ = b (Efun L) :=
        (Finset.mem_filter.1 (hNear h2)).2
      exact (hEfar L hnear).elim
  -- Dual basis of leave-one directions.
  have hydir : ∀ L : tU, ∃ y,
      ⟪a L.1, y⟫ = -1 ∧
      (∀ j : Fin n, ⟪a j, u⟫ = b j → j ≠ L.1 → ⟪a j, y⟫ = 0) ∧
      y ≠ 0 := by
    intro L
    exact leave_one_dir hu (hsimple u hu) L.1 (Finset.mem_filter.1 L.2).2
  choose yfun hyL hyorth hyne using hydir
  -- Each neighbour lies on the ray of its leave-one direction.
  have hwray : ∀ L : tU, ∃ t : ℝ, 0 < t ∧ wfun L = u + t • yfun L := by
    intro L
    let t : ℝ := -⟪a L.1, wfun L - u⟫
    have hδ : (wfun L - u) - t • yfun L = 0 := by
      have hker : ∀ j, ⟪a j, u⟫ = b j →
          ⟪a j, (wfun L - u) - t • yfun L⟫ = 0 := by
        intro j hjt
        by_cases hjL : j = L.1
        · subst hjL
          rw [inner_sub_right, inner_smul_right, hyL L]
          dsimp [t]
          ring
        · have hwj : ⟪a j, wfun L⟫ = b j := hkeptf L j hjt hjL
          have hyj : ⟪a j, yfun L⟫ = 0 := hyorth L j hjt hjL
          rw [inner_sub_right, inner_smul_right, inner_sub_right, hwj, hjt, hyj]
          ring
      exact extreme_tight_orthogonal hu hker
    have htpos : 0 < t := by
      have hLnot : ⟪a L.1, wfun L⟫ ≠ b L.1 := by
        intro htight
        have hcard : (Finset.univ.filter (fun j : Fin n =>
            ⟪a j, wfun L⟫ = b j)).card = d := hsimple (wfun L) (hwexf L)
        have hsub : tU.erase L.1 ∪ {H} ⊆
            Finset.univ.filter (fun j : Fin n => ⟪a j, wfun L⟫ = b j) := by
          intro j hj
          refine Finset.mem_filter.2 ⟨Finset.mem_univ j, ?_⟩
          rcases Finset.mem_union.1 hj with hjU | hjH
          · have hjne : j ≠ L.1 := (Finset.mem_erase.1 hjU).1
            have hjt : ⟪a j, u⟫ = b j :=
              (Finset.mem_filter.1 (Finset.mem_erase.1 hjU).2).2
            exact hkeptf L j hjt hjne
          · have : j = H := Finset.mem_singleton.1 hjH
            subst this
            rw [← hEH L]
            exact hEwf L
        have hcard' : (tU.erase L.1 ∪ {H}).card = d := by
          have hnot : H ∉ tU.erase L.1 := by
            intro hH
            exact hHnotU (Finset.mem_of_mem_erase hH)
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hnot),
            Finset.card_singleton, Finset.card_erase_of_mem L.2, hUcard]
          omega
        have hLmemW : L.1 ∈ Finset.univ.filter (fun j : Fin n =>
            ⟪a j, wfun L⟫ = b j) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, htight⟩
        have hLnotIn : L.1 ∉ tU.erase L.1 ∪ {H} := by
          intro h
          rcases Finset.mem_union.1 h with h1 | h2
          · exact (Finset.notMem_erase L.1 tU) h1
          · have : L.1 = H := Finset.mem_singleton.1 h2
            exact hHnotU (this ▸ L.2)
        have : (tU.erase L.1 ∪ {H}).card <
            (Finset.univ.filter (fun j : Fin n => ⟪a j, wfun L⟫ = b j)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
            ⟨hsub, fun heq => hLnotIn (heq.symm ▸ hLmemW)⟩)
        omega
      have : ⟪a L.1, wfun L⟫ < b L.1 :=
        lt_of_le_of_ne ((hwexf L).1 L.1) hLnot
      dsimp [t]
      rw [inner_sub_right]
      linarith [show ⟪a L.1, u⟫ = b L.1 from (Finset.mem_filter.1 L.2).2]
    refine ⟨t, htpos, ?_⟩
    have : wfun L - u = t • yfun L := eq_of_sub_eq_zero hδ
    calc
      wfun L = u + (wfun L - u) := by abel
      _ = u + t • yfun L := by rw [this]
  choose tfun htpos hwform using hwray
  have hHu : ⟪a H, u⟫ < b H :=
    lt_of_le_of_ne (hu.1 H) (hEuf L0s)
  have hyH : ∀ L : tU, ⟪a H, yfun L⟫ = (b H - ⟪a H, u⟫) / tfun L := by
    intro L
    have hwH : ⟪a H, wfun L⟫ = b H := by
      rw [← hEH L]; exact hEwf L
    have : ⟪a H, wfun L⟫ = ⟪a H, u⟫ + tfun L * ⟪a H, yfun L⟫ := by
      rw [hwform L]
      simp [inner_add_right, inner_smul_right]
    have ht0 : tfun L ≠ 0 := (htpos L).ne'
    field_simp [ht0]
    linarith
  have hInSimplex : ∀ x ∈ Hpoly a b,
      ∃ α : tU → ℝ, (∀ L, 0 ≤ α L) ∧ (∑ L, α L ≤ 1) ∧
        x = (1 - ∑ L, α L) • u + ∑ L, α L • wfun L := by
    intro x hx
    let c : tU → ℝ := fun L => -⟪a L.1, x - u⟫
    have hc0 : ∀ L, 0 ≤ c L := by
      intro L
      have hxL : ⟪a L.1, x⟫ ≤ b L.1 := hx L.1
      have huL : ⟪a L.1, u⟫ = b L.1 := (Finset.mem_filter.1 L.2).2
      dsimp [c]
      rw [inner_sub_right]
      linarith
    have hspan : x - u = ∑ L : tU, c L • yfun L := by
      let δ : EuclideanSpace ℝ (Fin d) :=
        x - u - ∑ L : tU, c L • yfun L
      have hker : ∀ j, ⟪a j, u⟫ = b j → ⟪a j, δ⟫ = 0 := by
        intro j hjt
        have hj : j ∈ tU := Finset.mem_filter.2 ⟨Finset.mem_univ j, hjt⟩
        dsimp [δ]
        rw [inner_sub_right, inner_sub_right, inner_sum]
        have hsum :
            ∑ L ∈ tU.attach, ⟪a j, c L • yfun L⟫ =
              c ⟨j, hj⟩ * ⟪a j, yfun ⟨j, hj⟩⟫ := by
          have hmem : ⟨j, hj⟩ ∈ tU.attach := Finset.mem_attach tU ⟨j, hj⟩
          have hsplit :=
            (Finset.add_sum_erase tU.attach
              (fun L => ⟪a j, c L • yfun L⟫) hmem).symm
          have hrest :
              ∑ L ∈ tU.attach.erase ⟨j, hj⟩, ⟪a j, c L • yfun L⟫ = 0 := by
            apply Finset.sum_eq_zero
            intro L hLmem
            have hneq : j ≠ L.1 := by
              intro hjeq
              have : L = ⟨j, hj⟩ := Subtype.ext hjeq.symm
              exact Finset.notMem_erase _ _ (this ▸ hLmem)
            have hy0 : ⟪a j, yfun L⟫ = 0 := hyorth L j hjt hneq
            simp [inner_smul_right, hy0]
          have hone : ⟪a j, c ⟨j, hj⟩ • yfun ⟨j, hj⟩⟫ =
              c ⟨j, hj⟩ * ⟪a j, yfun ⟨j, hj⟩⟫ := inner_smul_right _ _ _
          rw [hsplit, hrest, hone, add_zero]
        rw [hsum, hyL ⟨j, hj⟩]
        dsimp [c]
        rw [inner_sub_right]
        ring
      have hδ0 : δ = 0 := extreme_tight_orthogonal hu hker
      exact eq_of_sub_eq_zero hδ0
    let α : tU → ℝ := fun L => c L / tfun L
    have hα0 : ∀ L, 0 ≤ α L := fun L => div_nonneg (hc0 L) (htpos L).le
    have hαc : ∀ L, α L * tfun L = c L := fun L =>
      div_mul_cancel₀ _ (htpos L).ne'
    have hxH : ⟪a H, x⟫ ≤ b H := hx H
    have hαsum : ∑ L, α L ≤ 1 := by
      have hxexp : ⟪a H, x⟫ = ⟪a H, u⟫ + ∑ L : tU, c L * ⟪a H, yfun L⟫ := by
        have hxu : x = u + ∑ L : tU, c L • yfun L := by
          calc
            x = u + (x - u) := by abel
            _ = u + ∑ L : tU, c L • yfun L := by rw [hspan]
        rw [hxu, inner_add_right, inner_sum]
        simp [inner_smul_right]
      have hrew : ∑ L : tU, c L * ⟪a H, yfun L⟫ =
          (b H - ⟪a H, u⟫) * ∑ L, α L := by
        have hterm : ∀ L : tU, c L * ⟪a H, yfun L⟫ =
            (b H - ⟪a H, u⟫) * α L := by
          intro L
          rw [hyH L]
          dsimp [α]
          field_simp [(htpos L).ne']
        simp only [hterm, Finset.mul_sum]
      have hxexp' : ⟪a H, x⟫ = ⟪a H, u⟫ + (b H - ⟪a H, u⟫) * ∑ L, α L := by
        rw [hxexp, hrew]
      have hΔ : 0 < b H - ⟪a H, u⟫ := sub_pos.2 hHu
      have : ⟪a H, u⟫ + (b H - ⟪a H, u⟫) * ∑ L, α L ≤ b H := by
        rw [← hxexp']
        exact hxH
      nlinarith
    refine ⟨α, hα0, hαsum, ?_⟩
    have hxu : x = u + ∑ L : tU, c L • yfun L := by
      calc
        x = u + (x - u) := by abel
        _ = u + ∑ L : tU, c L • yfun L := by rw [hspan]
    have hsumα : ∑ L : tU, c L • yfun L = ∑ L : tU, α L • (wfun L - u) := by
      apply Finset.sum_congr rfl
      intro L _
      have hw : tfun L • yfun L = wfun L - u := by
        rw [hwform L, add_sub_cancel_left]
      rw [← hαc L, ← smul_smul, hw]
    rw [hsumα] at hxu
    have : u + ∑ L : tU, α L • (wfun L - u) =
        (1 - ∑ L, α L) • u + ∑ L, α L • wfun L := by
      have h1 :
          ∑ L ∈ tU.attach, α L • (wfun L - u) =
            (∑ L ∈ tU.attach, α L • wfun L) - (∑ L ∈ tU.attach, α L • u) := by
        simp only [smul_sub]
        exact Finset.sum_sub_distrib
          (f := fun L : tU => α L • wfun L)
          (g := fun L : tU => α L • u)
      have h2 : ∑ L ∈ tU.attach, α L • u = (∑ L ∈ tU.attach, α L) • u := by
        rw [← Finset.sum_smul]
      have h1' :
          ∑ L ∈ tU.attach, α L • (wfun L - u) =
            (∑ L ∈ tU.attach, α L • wfun L) - (∑ L ∈ tU.attach, α L) • u := by
        rw [← h2]; exact h1
      have hhead : ∀ σ : ℝ, u - σ • u = (1 - σ) • u := fun σ => by
        calc
          u - σ • u = (1 : ℝ) • u - σ • u := by rw [one_smul]
          _ = (1 - σ) • u := by rw [sub_smul]
      have hrearr : ∀ p q r : EuclideanSpace ℝ (Fin d),
          p + (q - r) = p - r + q := by
        intro p q r
        abel
      calc
        u + ∑ L ∈ tU.attach, α L • (wfun L - u) =
            u + ((∑ L ∈ tU.attach, α L • wfun L) -
              (∑ L ∈ tU.attach, α L) • u) := by
          rw [h1']
        _ = u - (∑ L ∈ tU.attach, α L) • u +
              ∑ L ∈ tU.attach, α L • wfun L := by
          rw [hrearr]
        _ = (1 - ∑ L ∈ tU.attach, α L) • u +
              ∑ L ∈ tU.attach, α L • wfun L := by
          rw [hhead]
    exact hxu.trans this
  -- z₁ is extreme in P and a convex combination of u and the neighbours,
  -- hence equals u or some neighbour, all of which are far from i.
  obtain ⟨α, hα0, hαsum, hzcomb⟩ := hInSimplex z₁ (extremePoints_subset hz₁)
  have hui : ⟪a i, u⟫ < b i := by
    refine lt_of_le_of_ne (hu.1 i) ?_
    intro h
    exact huRV (Or.inl h)
  have hwI : ∀ L : tU, ⟪a i, wfun L⟫ < b i := by
    intro L
    refine lt_of_le_of_ne ((hwexf L).1 i) ?_
    intro h
    exact hnone L (Or.inl h)
  have hzlt : ⟪a i, z₁⟫ < b i := by
    have hexp : ⟪a i, z₁⟫ =
        (1 - ∑ L, α L) * ⟪a i, u⟫ + ∑ L, α L * ⟪a i, wfun L⟫ := by
      rw [hzcomb, inner_add_right, inner_smul_right, inner_sum]
      simp [inner_smul_right]
    rw [hexp]
    have h1 : (1 - ∑ L, α L) * ⟪a i, u⟫ ≤ (1 - ∑ L, α L) * b i :=
      mul_le_mul_of_nonneg_left hui.le (sub_nonneg.2 hαsum)
    have h2 : ∑ L, α L * ⟪a i, wfun L⟫ ≤ ∑ L, α L * b i := by
      apply Finset.sum_le_sum
      intro L _
      exact mul_le_mul_of_nonneg_left (hwI L).le (hα0 L)
    have h3 : (1 - ∑ L, α L) * b i + (∑ L, α L * b i) = b i := by
      have hpull : (∑ L, α L * b i) = (∑ L, α L) * b i := by
        rw [← Finset.sum_mul]
      rw [hpull]
      ring
    have hstrict : (1 - ∑ L, α L) * ⟪a i, u⟫ + (∑ L, α L * ⟪a i, wfun L⟫) <
        (1 - ∑ L, α L) * b i + (∑ L, α L * b i) := by
      have hdiff :
          ((1 - ∑ L, α L) * b i + (∑ L, α L * b i)) -
            ((1 - ∑ L, α L) * ⟪a i, u⟫ + (∑ L, α L * ⟪a i, wfun L⟫)) =
          (1 - ∑ L, α L) * (b i - ⟪a i, u⟫) +
            (∑ L, α L * (b i - ⟪a i, wfun L⟫)) := by
        have hpull :
            (∑ L, α L * (b i - ⟪a i, wfun L⟫)) =
              (∑ L, α L * b i) - (∑ L, α L * ⟪a i, wfun L⟫) := by
          simp only [mul_sub]
          exact Finset.sum_sub_distrib
            (s := (Finset.univ : Finset tU))
            (f := fun L : tU => α L * b i)
            (g := fun L : tU => α L * ⟪a i, wfun L⟫)
        rw [hpull]
        ring
      have hpos : 0 <
          (1 - ∑ L, α L) * (b i - ⟪a i, u⟫) +
            ∑ L, α L * (b i - ⟪a i, wfun L⟫) := by
        have hu' : 0 < b i - ⟪a i, u⟫ := sub_pos.2 hui
        have hw' : ∀ L, 0 < b i - ⟪a i, wfun L⟫ := fun L => sub_pos.2 (hwI L)
        have hrest0 : 0 ≤ ∑ L, α L * (b i - ⟪a i, wfun L⟫) :=
          Finset.sum_nonneg fun L _ => mul_nonneg (hα0 L) (hw' L).le
        by_cases hσ1 : ∑ L, α L = 1
        · have hfirst : (1 - ∑ L, α L) * (b i - ⟪a i, u⟫) = 0 := by
            rw [hσ1, sub_self, zero_mul]
          rw [hfirst, zero_add]
          have hαne : ∃ L : tU, 0 < α L := by
            by_contra hall
            have hαle : ∀ L, α L ≤ 0 := fun L =>
              le_of_not_gt fun h => hall ⟨L, h⟩
            have : ∑ L, α L = 0 :=
              Finset.sum_eq_zero fun L _ => le_antisymm (hαle L) (hα0 L)
            exact (one_ne_zero : (1 : ℝ) ≠ 0) (hσ1.symm.trans this)
          obtain ⟨L, hLpos⟩ := hαne
          have hLone : 0 < α L * (b i - ⟪a i, wfun L⟫) :=
            mul_pos hLpos (hw' L)
          have hsplit :=
            (Finset.add_sum_erase Finset.univ
              (fun M => α M * (b i - ⟪a i, wfun M⟫)) (Finset.mem_univ L)).symm
          have hrest :
              0 ≤ ∑ M ∈ Finset.univ.erase L,
                α M * (b i - ⟪a i, wfun M⟫) :=
            Finset.sum_nonneg fun M _ => mul_nonneg (hα0 M) (hw' M).le
          linarith
        · have hσlt : ∑ L, α L < 1 := lt_of_le_of_ne hαsum hσ1
          have hwgt : 0 < 1 - ∑ L, α L := sub_pos.2 hσlt
          have : 0 < (1 - ∑ L, α L) * (b i - ⟪a i, u⟫) := mul_pos hwgt hu'
          linarith
      linarith
    linarith
  exact (lt_irrefl _ (hzi₁.symm ▸ hzlt)).elim



