-- Prove2me | solution 1 for Hirsch.ridge_visible_neighbor_of_n_le_two_d_add_two
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T16:29:21.834901+00:00
-- url     : https://prove2.me/submissions/2180ef1b-375f-437c-b624-70714c113781

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
    {d n : ℕ} (hn : n ≤ 2 * d + 1)
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
  have hRV (x : EuclideanSpace ℝ (Fin d)) : IsRidgeVisible a b i x ↔
      (⟪a i, x⟫ = b i ∨
        ∃ r : Fin n, r ≠ i ∧ ⟪a r, x⟫ = b r ∧
          ∃ y ∈ Hpoly a b, ⟪a i, y⟫ = b i ∧ ⟪a r, y⟫ = b r) := Iff.rfl
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
  -- Every tight row of u is far from i, since u is not ridge-visible.
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
  have hFarBd : tU.card + (t₁ ∪ t₂).card ≤ n := by
    have hunion : (tU ∪ (t₁ ∪ t₂)).card ≤ n := by
      simpa [Fintype.card_fin] using (tU ∪ (t₁ ∪ t₂)).card_le_univ
    have hinter : tU ∩ (t₁ ∪ t₂) = ∅ := Finset.disjoint_iff_inter_eq_empty.1 hdisj
    have hsum := Finset.card_union_add_card_inter tU (t₁ ∪ t₂)
    have hsum' : (tU ∪ (t₁ ∪ t₂)).card = tU.card + (t₁ ∪ t₂).card := by
      simpa [hinter] using hsum
    exact hsum'.symm.trans_le hunion
  have hUne : tU.Nonempty := by
    have : 0 < tU.card := by rw [hUcard]; exact hdpos
    exact Finset.card_pos.1 this
  obtain ⟨L, hLmem⟩ := hUne
  have hL : ⟪a L, u⟫ = b L := (Finset.mem_filter.1 hLmem).2
  obtain ⟨w, E, hwex, hadj, hEu, hEw, hkept⟩ :=
    simple_leave_one_neighbor hbd hu (hsimple u hu) L hL
  refine Or.inr ⟨w, hwex, hadj, ?_⟩
  by_cases hERV : IsRidgeVisible a b i w
  · exact hERV
  have hEne : E ≠ i := by
    intro hEi
    subst hEi
    exact hERV (Or.inl hEw)
  have hEmeet : ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a E, x⟫ = b E := by
    by_contra hnom
    have hEnotU : E ∉ tU := by
      intro hE
      exact hEu (Finset.mem_filter.1 hE).2
    have hTUEcard : (tU ∪ {E}).card = d + 1 := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hEnotU),
        Finset.card_singleton, hUcard]
    have hdisj' : Disjoint (tU ∪ {E}) (t₁ ∪ t₂) := by
      refine Finset.disjoint_left.2 ?_
      intro j hj hj12
      have hnear : j = i ∨ ∃ x ∈ Hpoly a b, ⟪a i, x⟫ = b i ∧ ⟪a j, x⟫ = b j :=
        (Finset.mem_filter.1 (hNear hj12)).2
      rcases Finset.mem_union.1 hj with hjU | hjE
      · exact hUfar j hjU hnear
      · have : j = E := Finset.mem_singleton.1 hjE
        subst this
        rcases hnear with hij | hx
        · exact hEne hij
        · exact hnom hx
    have hsumle : (tU ∪ {E}).card + (t₁ ∪ t₂).card ≤ n := by
      have hunion : ((tU ∪ {E}) ∪ (t₁ ∪ t₂)).card ≤ n := by
        simpa [Fintype.card_fin] using ((tU ∪ {E}) ∪ (t₁ ∪ t₂)).card_le_univ
      have hinter : (tU ∪ {E}) ∩ (t₁ ∪ t₂) = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.1 hdisj'
      have hsum := Finset.card_union_add_card_inter (tU ∪ {E}) (t₁ ∪ t₂)
      rw [hinter, Finset.card_empty, add_zero] at hsum
      exact hsum.symm.trans_le hunion
    have : d + 1 + (d + 1) ≤ n := by
      have := hsumle
      rw [hTUEcard] at this
      linarith
    linarith
  exact Or.inr ⟨E, hEne, hEw, hEmeet⟩


