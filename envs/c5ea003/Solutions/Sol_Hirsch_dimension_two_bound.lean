-- Prove2me | solution 1 for Hirsch.dimension_two_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T04:42:11.32002+00:00
-- url     : https://prove2.me/submissions/bbd46ed1-03da-4be8-baa7-2c890a8a75a2

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ActiveConstraints
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite

open scoped RealInnerProductSpace
open Hirsch

namespace HirschLib

/-! ## Walks -/

/-- A constant walk witnesses `DiamLE` between equal endpoints. -/
theorem diamLE_of_subsingleton {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v) :
    DiamLE P B := by
  intro u hu v hv
  exact ⟨fun _ => u, rfl, h u hu v hv, fun i _ => Or.inl rfl⟩

/-- One edge, then stay put: a walk of any positive length. -/
theorem diamLE_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (hB : 1 ≤ B)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v ∨ Adj P u v) :
    DiamLE P B := by
  intro u hu v hv
  rcases h u hu v hv with heq | hadj
  · exact ⟨fun _ => u, rfl, heq, fun i _ => Or.inl rfl⟩
  · have hB0 : B ≠ 0 := by omega
    refine ⟨fun i => if i = 0 then u else v, by simp, by simp [hB0], ?_⟩
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact Or.inr (by simpa using hadj)
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i + 1 ≠ 0 := by omega
      left; simp [hi0, hi1]

/-! ## Convex sets in a space of dimension at most one -/

/-- In a space of dimension at most one, a convex set with two distinct extreme
points is exactly the segment between them. -/
theorem eq_segment_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h1 : Module.finrank ℝ E ≤ 1) (P : Set E) (hP : Convex ℝ P)
    {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (hv : v ∈ Set.extremePoints ℝ P)
    (huv : u ≠ v) : P = segment ℝ u v := by
  classical
  set e : E := v - u with he
  have hene : e ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  -- the line through `u` and `v` is everything
  have hspan : Submodule.span ℝ ({e} : Set E) = ⊤ := by
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({e} : Set E)) = 1 :=
      finrank_span_singleton hene
    have h3 : 1 ≤ Module.finrank ℝ E := h2 ▸ Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hline : ∀ x : E, ∃ t : ℝ, x = u + t • e := by
    intro x
    have : x - u ∈ Submodule.span ℝ ({e} : Set E) := by rw [hspan]; trivial
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; abel⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := hline x
    have hvu : v = u + (1:ℝ) • e := by rw [he]; module
    -- `t < 0` would exhibit `u` inside an open segment of `P`
    have ht0 : 0 ≤ t := by
      by_contra hlt
      push_neg at hlt
      have hden : (0:ℝ) < 1 - t := by linarith
      refine huv (((mem_extremePoints.mp hu).2 _ hx _ (extremePoints_subset hv) ?_).2).symm
      refine ⟨1 / (1 - t), -t / (1 - t), div_pos one_pos hden,
        div_pos (by linarith) hden, by field_simp <;> ring, ?_⟩
      have h1 : (1:ℝ) / (1 - t) + -t / (1 - t) = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1 = 0 := by field_simp <;> ring
      rw [hvu]
      calc (1 / (1 - t)) • (u + t • e) + (-t / (1 - t)) • (u + (1:ℝ) • e)
          = ((1:ℝ) / (1 - t) + -t / (1 - t)) • u
            + ((1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1) • e := by module
        _ = u := by rw [h1, h2]; module
    -- `t > 1` would exhibit `v` inside an open segment of `P`
    have ht1 : t ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have hden : (0:ℝ) < t := by linarith
      refine huv (((mem_extremePoints.mp hv).2 _ (extremePoints_subset hu) _ hx ?_).1)
      refine ⟨(t - 1) / t, 1 / t, div_pos (by linarith) hden, div_pos one_pos hden,
        by field_simp <;> ring, ?_⟩
      have h1 : (t - 1) / t + 1 / t * 1 = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / t * t = 1 := by field_simp <;> ring
      rw [hvu]
      calc ((t - 1) / t) • u + (1 / t) • (u + t • e)
          = ((t - 1) / t + 1 / t * 1) • u + ((1:ℝ) / t * t) • e := by module
        _ = u + (1:ℝ) • e := by rw [h1, h2]; module
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [he]; module
  · exact hP.segment_subset (extremePoints_subset hu) (extremePoints_subset hv)


/-! ## H-polytopes -/

theorem hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hexp]
  have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
  have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

/-- If the polytope is bounded, every nonzero direction is cut off by some
inequality: no ray can survive inside a bounded set. -/
theorem exists_pos_inner_of_bounded {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) (e : EuclideanSpace ℝ (Fin d)) (he : e ≠ 0) :
    ∃ i, 0 < ⟪a i, e⟫ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbd
  have hepos : (0:ℝ) < ‖e‖ := norm_pos_iff.mpr he
  set t : ℝ := (R + ‖x0‖ + 1) / ‖e‖ with htdef
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hx0)
  have ht : 0 ≤ t := by rw [htdef]; positivity
  have hmem : x0 + t • e ∈ Hpoly a b := by
    intro i
    have hexp : ⟪a i, x0 + t • e⟫ = ⟪a i, x0⟫ + t * ⟪a i, e⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    rw [hexp]
    have h1 := hx0 i
    nlinarith [hcon i]
  have h1 := hR _ hmem
  have hnorm : ‖t • e‖ ≤ ‖x0 + t • e‖ + ‖x0‖ := by
    calc ‖t • e‖ = ‖(x0 + t • e) - x0‖ := by congr 1; abel
      _ ≤ ‖x0 + t • e‖ + ‖x0‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hnorm
  have hte : t * ‖e‖ = R + ‖x0‖ + 1 := by
    rw [htdef]; field_simp
  linarith

/-- In dimension at least one, a bounded nonempty H-polytope needs at least two
inequalities: one to cut off each of two opposite directions. -/
theorem two_le_of_bounded {d n : ℕ} (hd : 1 ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) : 2 ≤ n := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ (1:ℝ) with hedef
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x ⟨0, hd⟩) h
    simp [hedef] at this
  obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e he
  obtain ⟨j, hj⟩ := exists_pos_inner_of_bounded a b hne hbd (-e) (neg_ne_zero.mpr he)
  rw [inner_neg_right] at hj
  have hij : i ≠ j := by
    intro h; subst h; linarith
  haveI : Nontrivial (Fin n) := ⟨i, j, hij⟩
  have hcard := Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial (Fin n)›
  simpa using hcard

/-- **The Hirsch bound in dimension at most one.**  For `d = 0` the polytope is a
point; for `d = 1` it is a segment, its two extreme points are joined by the single
edge `P` itself, and boundedness forces `n ≥ 2`, so one step is available. -/
theorem dim_le_one_bound {d n : ℕ} (hd : d ≤ 1)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · refine diamLE_of_subsingleton _ _ fun u _ v _ => ?_
    exact Subsingleton.elim u v
  · have hd1' : d = 1 := le_antisymm hd hd1
    subst hd1'
    have h2 : 2 ≤ n := two_le_of_bounded le_rfl a b hne hbd
    refine diamLE_of_adj _ _ (by omega) fun u hu v hv => ?_
    by_cases huv : u = v
    · exact Or.inl huv
    · refine Or.inr ⟨huv, ?_⟩
      have hrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) ≤ 1 := by simp
      have hseg := eq_segment_of_finrank_le_one hrk _ (hpoly_convex a b) hu hv huv
      rw [← hseg]
      exact IsExtreme.refl ℝ _


/-- **Exposed faces are edges.**  If a linear functional attains its minimum over
`P` exactly on the segment `[u, v]`, then `u` and `v` are adjacent.  This is the
workhorse for exhibiting edges: extremeness of a minimizing face is immediate,
because an affine function that is minimal at an interior point of a segment must
be minimal at both of its endpoints. -/
theorem adj_of_exposed {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (u v : E) (huv : u ≠ v)
    (hmin : ∀ x ∈ P, t ≤ c x)
    (hface : {x | x ∈ P ∧ c x = t} = segment ℝ u v) : Adj P u v := by
  refine ⟨huv, ?_⟩
  rw [← hface]
  constructor
  · exact fun x hx => hx.1
  · rintro x₁ hx₁ x₂ hx₂ x ⟨hxP, hxt⟩ ⟨p, q, hp, hq, hpq, hx⟩
    have hc : c x = p * c x₁ + q * c x₂ := by
      rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hmin _ hx₁
    have h2 := hmin _ hx₂
    have h3 : p * c x₁ + q * c x₂ = t := by rw [← hc, hxt]
    have key : p * (c x₁ - t) + q * (c x₂ - t) = 0 := by
      linear_combination h3 - t * hpq
    have hz1 : 0 ≤ p * (c x₁ - t) := mul_nonneg hp.le (by linarith)
    have hz2 : 0 ≤ q * (c x₂ - t) := mul_nonneg hq.le (by linarith)
    have he1 : c x₁ = t := by
      have : p * (c x₁ - t) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hp)
      · linarith
    exact ⟨hx₁, he1⟩

/-- **A bounded H-polytope needs more inequalities than the ambient dimension.**
The map `x ↦ (⟪aᵢ, x⟫)ᵢ` is injective, since a vector in its kernel would give a
direction no inequality cuts off; so `d ≤ n`.  If `d = n` it is also surjective,
and pulling back `-e₀` produces a direction that no inequality cuts off after all. -/
theorem succ_le_of_bounded {d n : ℕ} (hd : 1 ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) : d + 1 ≤ n := by
  classical
  set T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x i => ⟪a i, x⟫
      map_add' := by intro x y; funext i; simp [inner_add_right]
      map_smul' := by intro r x; funext i; simp [real_inner_smul_right] } with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    by_contra hne0
    obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e hne0
    have : (T e) i = 0 := by rw [he]; rfl
    simp only [hT, LinearMap.coe_mk, AddHom.coe_mk] at this
    linarith
  have hdn : d ≤ n := by
    have h1 := LinearMap.finrank_le_finrank_of_injective (f := T) hinj
    simpa using h1
  rcases Nat.lt_or_ge d n with h | h
  · omega
  · -- `d = n` is impossible
    exfalso
    have hdeq : d = n := le_antisymm hdn h
    have hn : 0 < n := by omega
    have hrange : LinearMap.range T = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h2 : Module.finrank ℝ (LinearMap.range T) = d := by
        rw [LinearMap.finrank_range_of_inj hinj]; simp
      rw [h2]; simp [hdeq]
    set f : Fin n → ℝ := -(Pi.single (⟨0, hn⟩ : Fin n) (1:ℝ)) with hf
    obtain ⟨e, he⟩ : ∃ e, T e = f := by
      have hmem : f ∈ LinearMap.range T := by rw [hrange]; trivial
      exact hmem
    have hcoord : ∀ i, ⟪a i, e⟫ = f i := fun i => congrFun he i
    have hzero : f (⟨0, hn⟩ : Fin n) = -1 := by simp [hf]
    have he0 : e ≠ 0 := by
      intro h
      have h1 := hcoord ⟨0, hn⟩
      rw [h, hzero] at h1
      simp at h1
    obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e he0
    rw [hcoord i] at hi
    rcases eq_or_ne i (⟨0, hn⟩ : Fin n) with rfl | hne'
    · rw [hzero] at hi; linarith
    · have : f i = 0 := by simp [hf, hne']
      rw [this] at hi; linarith


/-- The minimising face of a linear functional over a convex hull is the hull of the
minimising generators. -/
theorem hull_inter_eq {E : Type*} [AddCommGroup E] [Module ℝ E] (V : Set E)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (hV : ∀ z ∈ V, t ≤ c z) (W : Set E)
    (hW : ∀ z ∈ V, c z = t → z ∈ W) (hWne : (V ∩ W).Nonempty) :
    ∀ x ∈ convexHull ℝ V, c x = t → x ∈ convexHull ℝ (V ∩ W) := by
  classical
  intro x hx hcx
  obtain ⟨wV, hwV⟩ := hWne
  rw [convexHull_eq] at hx
  obtain ⟨ι, s, wt, z, hw0, hw1, hzV, hcm⟩ := hx
  -- points carrying no weight may be replaced by a fixed minimiser
  have hsum : ∑ i ∈ s, wt i • z i = x := by
    rw [← hcm, Finset.centerMass, hw1]; simp
  have hct : ∑ i ∈ s, wt i * (c (z i) - t) = 0 := by
    have h1 : ∑ i ∈ s, wt i * c (z i) = t := by
      have : c x = ∑ i ∈ s, wt i * c (z i) := by
        rw [← hsum, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
      rw [← this, hcx]
    have h2 : ∑ i ∈ s, wt i * t = t := by rw [← Finset.sum_mul, hw1, one_mul]
    have : ∑ i ∈ s, wt i * (c (z i) - t)
        = (∑ i ∈ s, wt i * c (z i)) - ∑ i ∈ s, wt i * t := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h1, h2, sub_self]
  have hterm : ∀ i ∈ s, wt i * (c (z i) - t) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hct
    exact fun i hi => mul_nonneg (hw0 i hi) (by linarith [hV _ (hzV i hi)])
  -- replace zero-weight points by `wV`
  set z' : ι → E := fun i => if wt i = 0 then wV else z i with hz'
  have hz'mem : ∀ i ∈ s, z' i ∈ V ∩ W := by
    intro i hi
    by_cases h0 : wt i = 0
    · simp only [hz', if_pos h0]
      exact hwV
    · simp only [hz', if_neg h0]
      have := hterm i hi
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · exact ⟨hzV i hi, hW _ (hzV i hi) (by linarith)⟩
  have hsum' : ∑ i ∈ s, wt i • z' i = x := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : wt i = 0
    · simp [h0]
    · simp [hz', if_neg h0]
  rw [← hsum', convexHull_eq]
  refine ⟨ι, s, wt, z', hw0, hw1, hz'mem, ?_⟩
  rw [Finset.centerMass, hw1]
  simp

/-- **Building an edge from a separating functional.**  If `P` is the convex hull of
`V` and a linear functional attains its minimum over `V` exactly at the two points
`u ≠ w`, then `u` and `w` are adjacent in `P`. -/
theorem adj_of_separating {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V P : Set E) (hP : P = convexHull ℝ V)
    (c : E →ₗ[ℝ] ℝ) (t : ℝ) (u w : E) (huw : u ≠ w)
    (huV : u ∈ V) (hwV : w ∈ V) (hu : c u = t) (hw : c w = t)
    (hother : ∀ z ∈ V, z ≠ u → z ≠ w → t < c z) : Adj P u w := by
  classical
  have hVge : ∀ z ∈ V, t ≤ c z := by
    intro z hz
    by_cases h1 : z = u
    · rw [h1, hu]
    by_cases h2 : z = w
    · rw [h2, hw]
    · exact (hother z hz h1 h2).le
  have hmin : ∀ x ∈ P, t ≤ c x := by
    rw [hP]
    refine convexHull_min hVge ?_
    exact convex_halfSpace_ge (LinearMap.isLinear c) t
  have hVW : V ∩ ({u, w} : Set E) = ({u, w} : Set E) := by
    apply Set.inter_eq_right.mpr
    rintro z (rfl | rfl)
    · exact huV
    · exact hwV
  refine adj_of_exposed P c t u w huw hmin ?_
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨hxP, hxt⟩
    rw [hP] at hxP
    have := hull_inter_eq V c t hVge ({u, w} : Set E)
      (fun z hz hz' => by
        by_contra hcon
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
        exact absurd hz' (ne_of_gt (hother z hz hcon.1 hcon.2)))
      ⟨u, huV, Or.inl rfl⟩ x hxP hxt
    rwa [hVW, convexHull_pair] at this
  · intro x hx
    have hseg : segment ℝ u w ⊆ P := by
      rw [hP]
      exact (convex_convexHull ℝ V).segment_subset (subset_convexHull ℝ V huV)
        (subset_convexHull ℝ V hwV)
    refine ⟨hseg hx, ?_⟩
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hx
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hu, hw]
    linear_combination t * hpq


/-- **Rotating a supporting functional.**  Let `g` be minimised over `V` uniquely at
`u`, and let `c` be any functional that `u` does *not* minimise.  Rotating `g` towards
`c` — that is, following `c + λ g` as `λ` decreases from `+∞` — the vertex `u` stops
being the unique minimiser at a first value `λ > 0`, where a second vertex `w` joins
it on the supporting hyperplane.  That `w` has strictly smaller `c`-value, so this is
simultaneously the improving-direction step of the simplex method. -/
theorem exists_rotated_functional {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Finset E) (u : E) (g c : E →ₗ[ℝ] ℝ)
    (hg : ∀ z ∈ V, z ≠ u → g u < g z) (hex : ∃ z ∈ V, c z < c u) :
    ∃ (lam : ℝ) (w : E), 0 < lam ∧ w ∈ V ∧ w ≠ u ∧ c w < c u ∧
      c w + lam * g w = c u + lam * g u ∧
      ∀ z ∈ V, c u + lam * g u ≤ c z + lam * g z := by
  classical
  set S := V.filter (fun z => c z < c u) with hS
  have hSne : S.Nonempty := by
    obtain ⟨z, hzV, hzc⟩ := hex
    exact ⟨z, Finset.mem_filter.mpr ⟨hzV, hzc⟩⟩
  set r : E → ℝ := fun z => (c u - c z) / (g z - g u) with hr
  obtain ⟨w, hwS, hwmax⟩ := S.exists_max_image r hSne
  have hwV : w ∈ V := (Finset.mem_filter.mp hwS).1
  have hwc : c w < c u := (Finset.mem_filter.mp hwS).2
  have hwu : w ≠ u := by intro h; rw [h] at hwc; exact lt_irrefl _ hwc
  have hgw : g u < g w := hg w hwV hwu
  have hden : (0:ℝ) < g w - g u := by linarith
  have hne : g w - g u ≠ 0 := ne_of_gt hden
  have hpos : 0 < r w := div_pos (by linarith) hden
  refine ⟨r w, w, hpos, hwV, hwu, hwc, ?_, ?_⟩
  · have : r w * (g w - g u) = c u - c w := by
      rw [hr]; field_simp
    linarith
  · intro z hzV
    rcases eq_or_ne z u with rfl | hzu
    · exact le_refl _
    · have hgz : g u < g z := hg z hzV hzu
      have hdz : (0:ℝ) < g z - g u := by linarith
      rcases lt_or_ge (c z) (c u) with hlt | hge
      · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hzV, hlt⟩
        have hle := hwmax z hzS
        have hkey : c u - c z ≤ r w * (g z - g u) := by
          rw [hr, div_le_iff₀ hdz] at hle
          exact hle
        linarith
      · nlinarith


/-- The middle of three distinct collinear points of `P` is never extreme. -/
theorem not_extreme_of_between {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (z₀ e : E) (he : e ≠ 0) (r₁ r₂ r₃ : ℝ) (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (h1 : z₀ + r₁ • e ∈ P) (h3 : z₀ + r₃ • e ∈ P) :
    z₀ + r₂ • e ∉ Set.extremePoints ℝ P := by
  intro hmid
  have hd : (0:ℝ) < r₃ - r₁ := by linarith
  set p : ℝ := (r₃ - r₂) / (r₃ - r₁) with hp
  set q : ℝ := (r₂ - r₁) / (r₃ - r₁) with hq
  have hp0 : 0 < p := div_pos (by linarith) hd
  have hq0 : 0 < q := div_pos (by linarith) hd
  have hpq : p + q = 1 := by rw [hp, hq]; field_simp; ring
  have hcomb : p • (z₀ + r₁ • e) + q • (z₀ + r₃ • e) = z₀ + r₂ • e := by
    have hcoef : p * r₁ + q * r₃ = r₂ := by rw [hp, hq]; field_simp; ring
    calc p • (z₀ + r₁ • e) + q • (z₀ + r₃ • e)
        = (p + q) • z₀ + (p * r₁ + q * r₃) • e := by module
      _ = z₀ + r₂ • e := by rw [hpq, hcoef]; module
  have hopen : z₀ + r₂ • e ∈ openSegment ℝ (z₀ + r₁ • e) (z₀ + r₃ • e) :=
    ⟨p, q, hp0, hq0, hpq, hcomb⟩
  have heq := (mem_extremePoints.mp hmid).2 _ h1 _ h3 hopen
  have : (r₁ - r₂) • e = 0 := by
    have := heq.1
    have h' : z₀ + r₁ • e - (z₀ + r₂ • e) = 0 := by rw [this]; abel
    calc (r₁ - r₂) • e = z₀ + r₁ • e - (z₀ + r₂ • e) := by module
      _ = 0 := h'
  rcases smul_eq_zero.mp this with h | h
  · have : r₁ = r₂ := by linarith [sub_eq_zero.mp h]
    linarith
  · exact he h

/-- **At most two vertices on a supporting line.**  In a plane, a nonzero linear
functional is constant on a line, and three distinct extreme points cannot be
collinear. -/
theorem card_le_two_on_level {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h2 : Module.finrank ℝ E ≤ 2) (P : Set E)
    (cc : E →ₗ[ℝ] ℝ) (hc : cc ≠ 0) (t : ℝ)
    {z₁ z₂ z₃ : E} (h1 : z₁ ∈ Set.extremePoints ℝ P) (hz2 : z₂ ∈ Set.extremePoints ℝ P)
    (h3 : z₃ ∈ Set.extremePoints ℝ P)
    (e1 : cc z₁ = t) (e2 : cc z₂ = t) (e3 : cc z₃ = t)
    (n12 : z₁ ≠ z₂) (n13 : z₁ ≠ z₃) (n23 : z₂ ≠ z₃) : False := by
  classical
  -- the differences all lie in `ker cc`, which has dimension at most one
  have hker : Module.finrank ℝ (LinearMap.ker cc) ≤ 1 := by
    have hrange : 1 ≤ Module.finrank ℝ (LinearMap.range cc) := by
      obtain ⟨x, hx⟩ : ∃ x, cc x ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hc (LinearMap.ext fun y => by simp [hcon y])
      haveI : Nontrivial (LinearMap.range cc) := by
        refine ⟨⟨⟨cc x, ⟨x, rfl⟩⟩, 0, ?_⟩⟩
        simpa [Subtype.ext_iff] using hx
      exact Module.finrank_pos
    have := LinearMap.finrank_range_add_finrank_ker cc
    omega
  set e : E := z₂ - z₁ with he
  have hene : e ≠ 0 := sub_ne_zero.mpr (Ne.symm n12)
  have hemem : e ∈ LinearMap.ker cc := by
    simp [LinearMap.mem_ker, he, map_sub, e1, e2]
  have hspan : Submodule.span ℝ ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _) = ⊤ := by
    have hne0 : (⟨e, hemem⟩ : LinearMap.ker cc) ≠ 0 := by
      simpa [Subtype.ext_iff] using hene
    have hfr : Module.finrank ℝ (Submodule.span ℝ
        ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _)) = 1 := finrank_span_singleton hne0
    have hle : 1 ≤ Module.finrank ℝ (LinearMap.ker cc) := hfr ▸ Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hparam : ∀ z : E, cc z = t → ∃ r : ℝ, z = z₁ + r • e := by
    intro z hz
    have hmem : (⟨z - z₁, by simp [LinearMap.mem_ker, map_sub, hz, e1]⟩ :
        LinearMap.ker cc) ∈ Submodule.span ℝ ({(⟨e, hemem⟩ : LinearMap.ker cc)} : Set _) := by
      rw [hspan]; trivial
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨r, hrr⟩ := hmem
    have hcoe : r • e = z - z₁ := by
      have h' := congrArg Subtype.val hrr
      simpa using h'
    exact ⟨r, by rw [hcoe]; abel⟩
  obtain ⟨r₁, hr₁⟩ := hparam z₁ e1
  obtain ⟨r₂, hr₂⟩ := hparam z₂ e2
  obtain ⟨r₃, hr₃⟩ := hparam z₃ e3
  have hinj : ∀ (s s' : ℝ), z₁ + s • e = z₁ + s' • e → s = s' := by
    intro s s' hss
    have : (s - s') • e = 0 := by
      have h' : s • e - s' • e = 0 := by
        have := hss
        have h2' : (z₁ + s • e) - (z₁ + s' • e) = 0 := by rw [this]; abel
        calc s • e - s' • e = (z₁ + s • e) - (z₁ + s' • e) := by abel
          _ = 0 := h2'
      rw [sub_smul]; exact h'
    rcases smul_eq_zero.mp this with h | h
    · linarith [sub_eq_zero.mp h]
    · exact absurd h hene
  have d12 : r₁ ≠ r₂ := fun h => n12 (by rw [hr₁, hr₂, h])
  have d13 : r₁ ≠ r₃ := fun h => n13 (by rw [hr₁, hr₃, h])
  have d23 : r₂ ≠ r₃ := fun h => n23 (by rw [hr₂, hr₃, h])
  -- the middle parameter gives a non-extreme point
  have key : ∀ (x y z : E) (rx ry rz : ℝ), x = z₁ + rx • e → y = z₁ + ry • e →
      z = z₁ + rz • e → rx < ry → ry < rz → x ∈ Set.extremePoints ℝ P →
      z ∈ Set.extremePoints ℝ P → y ∈ Set.extremePoints ℝ P → False := by
    intro x y z rx ry rz hx hy hz hxy hyz hxe hze hye
    refine not_extreme_of_between P z₁ e hene rx ry rz hxy hyz ?_ ?_ ?_
    · rw [← hx]; exact hxe.1
    · rw [← hz]; exact hze.1
    · rw [← hy]; exact hye
  rcases lt_trichotomy r₁ r₂ with h12' | h12' | h12'
  · rcases lt_trichotomy r₂ r₃ with h23' | h23' | h23'
    · exact key z₁ z₂ z₃ r₁ r₂ r₃ hr₁ hr₂ hr₃ h12' h23' h1 h3 hz2
    · exact d23 h23'
    · rcases lt_trichotomy r₁ r₃ with h13' | h13' | h13'
      · exact key z₁ z₃ z₂ r₁ r₃ r₂ hr₁ hr₃ hr₂ h13' h23' h1 hz2 h3
      · exact d13 h13'
      · exact key z₃ z₁ z₂ r₃ r₁ r₂ hr₃ hr₁ hr₂ h13' h12' h3 hz2 h1
  · exact d12 h12'
  · rcases lt_trichotomy r₁ r₃ with h13' | h13' | h13'
    · exact key z₂ z₁ z₃ r₂ r₁ r₃ hr₂ hr₁ hr₃ h12' h13' hz2 h3 h1
    · exact d13 h13'
    · rcases lt_trichotomy r₂ r₃ with h23' | h23' | h23'
      · exact key z₂ z₃ z₁ r₂ r₃ r₁ hr₂ hr₃ hr₁ h23' h13' hz2 h1 h3
      · exact d23 h23'
      · exact key z₃ z₂ z₁ r₃ r₂ r₁ hr₃ hr₂ hr₁ h23' h12' h3 h1 hz2


/-! ## Coordinates in the plane -/

/-- The standard basis vectors of the plane. -/
noncomputable abbrev pe (i : Fin 2) : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single i (1:ℝ)

theorem pe_apply (i j : Fin 2) : pe i j = if j = i then (1:ℝ) else 0 := by
  simp [pe, EuclideanSpace.single_apply]

theorem plane_ext (x : EuclideanSpace ℝ (Fin 2)) : x = x 0 • pe 0 + x 1 • pe 1 := by
  refine PiLp.ext fun j => ?_
  fin_cases j <;> simp [pe_apply]

theorem plane_eval (g : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    g x = x 0 * g (pe 0) + x 1 * g (pe 1) := by
  conv_lhs => rw [plane_ext x]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Rotation by a quarter turn, as a linear map on the plane. -/
noncomputable def rot : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := (-(x 1)) • pe 0 + (x 0) • pe 1
  map_add' x y := by
    simp only [PiLp.add_apply]
    module
  map_smul' r x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    module

theorem rot_pe0 : rot (pe 0) = pe 1 := by
  simp [rot, pe_apply]

theorem rot_pe1 : rot (pe 1) = -pe 0 := by
  simp [rot]

/-- A quarter turn produces a functional independent from the given one. -/
theorem perp_indep (g : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ) (hg : g ≠ 0) (α β : ℝ)
    (h : α • g + β • (g.comp rot) = 0) : α = 0 ∧ β = 0 := by
  have hne : g (pe 0) ≠ 0 ∨ g (pe 1) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hg (LinearMap.ext fun x => by rw [plane_eval g x, hcon.1, hcon.2]; simp)
  have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => f (pe 0)) h
  have h1 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ => f (pe 1)) h
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, smul_eq_mul, rot_pe0, rot_pe1, map_neg] at h0 h1
  -- `α a + β b = 0` and `α b - β a = 0` with `(a,b) ≠ 0`
  have hsq : ∀ r : ℝ, r ≠ 0 → 0 < r ^ 2 := by
    intro r hr
    rcases lt_trichotomy r 0 with h | h | h
    · nlinarith
    · exact absurd h hr
    · nlinarith
  have hpos : 0 < g (pe 0) ^ 2 + g (pe 1) ^ 2 := by
    rcases hne with hA | hB
    · nlinarith [hsq _ hA, sq_nonneg (g (pe 1))]
    · nlinarith [hsq _ hB, sq_nonneg (g (pe 0))]
  constructor
  · have hz : α * (g (pe 0) ^ 2 + g (pe 1) ^ 2) = 0 := by
      linear_combination g (pe 0) * h0 + g (pe 1) * h1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)
  · have hz : β * (g (pe 0) ^ 2 + g (pe 1) ^ 2) = 0 := by
      linear_combination g (pe 1) * h0 - g (pe 0) * h1
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)


/-- The plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The first coordinate, as a nonzero functional on the plane. -/
noncomputable def coord0 : E2 →ₗ[ℝ] ℝ where
  toFun x := x 0
  map_add' := by intro x y; simp
  map_smul' := by intro r x; simp

theorem coord0_pe0 : coord0 (pe 0) = 1 := by simp [coord0, pe_apply]

/-- A strict functional at `u` can always be perturbed so that no rotation towards `c`
degenerates to the zero functional. -/
theorem exists_strict_avoiding (V : Finset E2) (u : E2) (g : E2 →ₗ[ℝ] ℝ)
    (hg : ∀ z ∈ V, z ≠ u → g u < g z) (hV : ∃ z ∈ V, z ≠ u)
    (c : E2 →ₗ[ℝ] ℝ) (hc : c ≠ 0) :
    ∃ g' : E2 →ₗ[ℝ] ℝ, (∀ z ∈ V, z ≠ u → g' u < g' z) ∧ ∀ lam : ℝ, c + lam • g' ≠ 0 := by
  classical
  by_cases hgood : ∀ lam : ℝ, c + lam • g ≠ 0
  · exact ⟨g, hg, hgood⟩
  push_neg at hgood
  obtain ⟨lam₀, hlam₀⟩ := hgood
  have hgne : g ≠ 0 := by
    obtain ⟨z, hzV, hzu⟩ := hV
    intro h
    have := hg z hzV hzu
    rw [h] at this
    simp at this
  set h : E2 →ₗ[ℝ] ℝ := g.comp rot with hh
  set T := V.filter (fun z => z ≠ u) with hT
  have hTne : T.Nonempty := by
    obtain ⟨z, hzV, hzu⟩ := hV
    exact ⟨z, Finset.mem_filter.mpr ⟨hzV, hzu⟩⟩
  set δ : ℝ := T.inf' hTne (fun z => g z - g u) with hδ
  set M : ℝ := T.sup' hTne (fun z => |h u - h z|) with hM
  have hδpos : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro z hz
    have := Finset.mem_filter.mp hz
    linarith [hg z this.1 this.2]
  have hMnn : 0 ≤ M := by
    obtain ⟨z, hz⟩ := hTne
    exact le_trans (abs_nonneg _) (Finset.le_sup' (fun z => |h u - h z|) hz)
  set ε : ℝ := δ / (2 * (M + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  refine ⟨g + ε • h, ?_, ?_⟩
  · intro z hzV hzu
    have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hzV, hzu⟩
    have h1 : δ ≤ g z - g u := Finset.inf'_le (fun z => g z - g u) hzT
    have h2 : |h u - h z| ≤ M := Finset.le_sup' (fun z => |h u - h z|) hzT
    have h3 : h u - h z ≤ M := le_trans (le_abs_self _) h2
    have h4 : ε * M < δ := by
      rw [hε]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith
  · intro lam heq
    have hz : (lam - lam₀) • g + (lam * ε) • h = 0 := by
      have hc' : c = (-lam₀) • g := by
        have := hlam₀
        have : c + lam₀ • g = 0 := this
        ext x
        have := congrArg (fun f : E2 →ₗ[ℝ] ℝ => f x) this
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
          smul_eq_mul] at this
        simp only [LinearMap.smul_apply, smul_eq_mul]
        linarith
      ext x
      have := congrArg (fun f : E2 →ₗ[ℝ] ℝ => f x) heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul] at this
      rw [hc'] at this
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at this
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
        smul_eq_mul]
      linarith
    obtain ⟨ha, hb⟩ := perp_indep g hgne _ _ hz
    have hlam0 : lam = 0 := by
      rcases mul_eq_zero.mp hb with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hεpos)
    have : lam₀ = 0 := by linarith [ha, hlam0]
    apply hc
    have : c + (0:ℝ) • g = 0 := by rw [← this]; exact hlam₀
    simpa using this


/-- **The improving-edge step in the plane.**  If `u` is a vertex at which the linear
functional `c` is not minimal, then some edge at `u` leads to a vertex with strictly
smaller `c`-value.  The rotated supporting functional carries exactly two vertices,
because a supporting line of a planar polytope cannot hold three. -/
theorem improving_edge_plane (V : Finset E2) (P : Set E2)
    (hP : P = convexHull ℝ (V : Set E2))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (u : E2) (hu : u ∈ V) (g : E2 →ₗ[ℝ] ℝ) (hg : ∀ z ∈ V, z ≠ u → g u < g z)
    (c : E2 →ₗ[ℝ] ℝ) (hex : ∃ z ∈ V, c z < c u) :
    ∃ w ∈ V, c w < c u ∧ Adj P u w := by
  classical
  obtain ⟨z₀, hz₀V, hz₀c⟩ := hex
  have hz₀u : z₀ ≠ u := by intro h; rw [h] at hz₀c; exact lt_irrefl _ hz₀c
  have hc : c ≠ 0 := by intro h; rw [h] at hz₀c; simp at hz₀c
  obtain ⟨g', hg', havoid⟩ := exists_strict_avoiding V u g hg ⟨z₀, hz₀V, hz₀u⟩ c hc
  obtain ⟨lam, w, hlam, hwV, hwu, hwc, hfeq, hfmin⟩ :=
    exists_rotated_functional V u g' c hg' ⟨z₀, hz₀V, hz₀c⟩
  set f : E2 →ₗ[ℝ] ℝ := c + lam • g' with hf
  have hfapp : ∀ x, f x = c x + lam * g' x := by intro x; simp [hf]
  have hfne : f ≠ 0 := havoid lam
  have hfw : f w = f u := by rw [hfapp, hfapp]; linarith
  have hrk : Module.finrank ℝ E2 ≤ 2 := by simp
  refine ⟨w, hwV, hwc, ?_⟩
  refine adj_of_separating (V : Set E2) P hP f (f u) u w (Ne.symm hwu)
    (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hwV) rfl hfw ?_
  intro z hzV hzu hzw
  have hzV' : z ∈ V := Finset.mem_coe.mp hzV
  have hge : f u ≤ f z := by rw [hfapp, hfapp]; exact hfmin z hzV'
  rcases lt_or_eq_of_le hge with h | h
  · exact h
  · exact absurd (card_le_two_on_level hrk P f hfne (f u)
      (hVext u hu) (hVext w hwV) (hVext z hzV') rfl hfw h.symm
      (Ne.symm hwu) (Ne.symm hzu) (Ne.symm hzw)) (fun x => x)


/-- **Every vertex of a two-dimensional polytope has two neighbours.**  Rotating the
supporting functional at `u` in both directions produces neighbours on either side of a
level line through `u`; such a line exists because the vertices do not all lie on one
line. -/
theorem two_neighbours_plane (V : Finset E2) (P : Set E2)
    (hP : P = convexHull ℝ (V : Set E2))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hnl : ∀ (q : E2 →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, q z = t) → q = 0)
    (u : E2) (hu : u ∈ V) (g : E2 →ₗ[ℝ] ℝ) (hg : ∀ z ∈ V, z ≠ u → g u < g z) :
    ∃ w₁ ∈ V, ∃ w₂ ∈ V, w₁ ≠ w₂ ∧ Adj P u w₁ ∧ Adj P u w₂ := by
  classical
  set h : E2 →ₗ[ℝ] ℝ := g.comp rot with hh
  set ρ : E2 → ℝ := fun z => (h z - h u) / (g z - g u) with hρ
  -- a functional taking values on both sides of its value at `u`
  have hsplit : ∃ cc : E2 →ₗ[ℝ] ℝ, (∃ z ∈ V, cc z < cc u) ∧ (∃ z ∈ V, cc u < cc z) := by
    by_cases hall : ∃ z₁ ∈ V, ∃ z₂ ∈ V, z₁ ≠ u ∧ z₂ ≠ u ∧ ρ z₁ ≠ ρ z₂
    · obtain ⟨z₁, hz₁, z₂, hz₂, hz₁u, hz₂u, hne⟩ := hall
      set c₀ : ℝ := (ρ z₁ + ρ z₂) / 2 with hc₀
      refine ⟨h - c₀ • g, ?_, ?_⟩
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨z₁, hz₁, ?_⟩
          have hd : 0 < g z₁ - g u := by linarith [hg z₁ hz₁ hz₁u]
          have hr : ρ z₁ < c₀ := by rw [hc₀]; linarith
          have hval : h z₁ - h u = ρ z₁ * (g z₁ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
        · refine ⟨z₂, hz₂, ?_⟩
          have hd : 0 < g z₂ - g u := by linarith [hg z₂ hz₂ hz₂u]
          have hr : ρ z₂ < c₀ := by rw [hc₀]; linarith
          have hval : h z₂ - h u = ρ z₂ * (g z₂ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
      · rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨z₂, hz₂, ?_⟩
          have hd : 0 < g z₂ - g u := by linarith [hg z₂ hz₂ hz₂u]
          have hr : c₀ < ρ z₂ := by rw [hc₀]; linarith
          have hval : h z₂ - h u = ρ z₂ * (g z₂ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
        · refine ⟨z₁, hz₁, ?_⟩
          have hd : 0 < g z₁ - g u := by linarith [hg z₁ hz₁ hz₁u]
          have hr : c₀ < ρ z₁ := by rw [hc₀]; linarith
          have hval : h z₁ - h u = ρ z₁ * (g z₁ - g u) := by
            rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          nlinarith
    · -- all ratios agree: the vertices lie on a line, contradicting `hnl`
      exfalso
      push_neg at hall
      have hex_ne : ∃ z ∈ V, z ≠ u := by
        by_contra hcon
        push_neg at hcon
        have hall0 : ∀ q : E2 →ₗ[ℝ] ℝ, q = 0 :=
          fun q => hnl q (q u) (fun z hz => by rw [hcon z hz])
        have h0 := hall0 coord0
        have h1 : coord0 (pe 0) = 1 := coord0_pe0
        rw [h0] at h1
        simp at h1
      obtain ⟨z₀, hz₀V, hz₀u⟩ := hex_ne
      have hgne : g ≠ 0 := by
        intro hz
        have := hg z₀ hz₀V hz₀u
        rw [hz] at this
        simp at this
      set c₀ : ℝ := ρ z₀ with hc₀
      have hconst : ∀ z ∈ V, (h - c₀ • g) z = (h - c₀ • g) u := by
        intro z hzV
        rcases eq_or_ne z u with rfl | hzu
        · rfl
        · have hr : ρ z = c₀ := by
            by_contra hcon
            exact hcon (hall z hzV z₀ hz₀V hzu hz₀u)
          have hd : 0 < g z - g u := by linarith [hg z hzV hzu]
          have hval : h z - h u = ρ z * (g z - g u) := by rw [hρ]; field_simp
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          rw [hr] at hval
          linarith
      have hzero := hnl (h - c₀ • g) ((h - c₀ • g) u) hconst
      have hcomb : (-c₀) • g + (1:ℝ) • h = 0 := by
        rw [← hzero]; ext x
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          smul_eq_mul, one_mul]
        ring
      obtain ⟨-, hb⟩ := perp_indep g hgne _ _ hcomb
      exact absurd hb one_ne_zero
  obtain ⟨cc, hlt, hgt⟩ := hsplit
  obtain ⟨w₁, hw₁V, hw₁c, hw₁adj⟩ := improving_edge_plane V P hP hVext u hu g hg cc hlt
  obtain ⟨w₂, hw₂V, hw₂c, hw₂adj⟩ := improving_edge_plane V P hP hVext u hu g hg (-cc)
    (by obtain ⟨z, hzV, hz⟩ := hgt; exact ⟨z, hzV, by simpa using hz⟩)
  refine ⟨w₁, hw₁V, w₂, hw₂V, ?_, hw₁adj, hw₂adj⟩
  intro heq
  rw [heq] at hw₁c
  simp only [LinearMap.neg_apply, neg_lt_neg_iff] at hw₂c
  linarith

end HirschLib

open Hirsch

namespace HirschWalk

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `Reach P L u v`: a walk of exactly `L` steps from `u` to `v`, each step either
stationary or along an edge.  This is the body of `DiamLE`. -/
def Reach (P : Set E) (L : ℕ) (u v : E) : Prop :=
  ∃ w : ℕ → E, w 0 = u ∧ w L = v ∧ ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))

theorem reach_zero (P : Set E) (u : E) : Reach P 0 u u :=
  ⟨fun _ => u, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem reach_succ (P : Set E) (L : ℕ) (u v : E) (h : Reach P L u v) :
    Reach P (L + 1) u v := by
  classical
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => if i ≤ L then w i else v, by simpa using h0, by simp, ?_⟩
  intro i hi
  rcases lt_or_ge i L with h1 | h1
  · have hi1 : i + 1 ≤ L := h1
    simp only [if_pos h1.le, if_pos hi1]
    exact hstep i h1
  · have hiL : i = L := by omega
    subst hiL
    left
    simp [hL]

theorem reach_mono (P : Set E) {L L' : ℕ} (hLL : L ≤ L') {u v : E} (h : Reach P L u v) :
    Reach P L' u v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hLL
  clear hLL
  induction k with
  | zero => simpa using h
  | succ m ih => exact (Nat.add_succ L m) ▸ reach_succ P _ u v ih

/-- `DiamLE` is exactly reachability in `B` steps between vertices. -/
theorem diamLE_of_reach (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P,
      ∃ L ≤ B, Reach P L u v) : DiamLE P B := by
  intro u hu v hv
  obtain ⟨L, hLB, hL⟩ := h u hu v hv
  exact reach_mono P hLB hL

/-- Splicing out a repeat shortens a walk. -/
theorem reach_of_repeat (P : Set E) (L : ℕ) (u v : E) (w : ℕ → E)
    (h0 : w 0 = u) (hL : w L = v)
    (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1)))
    {i j : ℕ} (hij : i < j) (hjL : j ≤ L) (heq : w i = w j) :
    Reach P (L - (j - i)) u v := by
  classical
  refine ⟨fun k => if k ≤ i then w k else w (k + (j - i)), ?_, ?_, ?_⟩
  · simpa using h0
  · dsimp only
    by_cases hc : L - (j - i) ≤ i
    · have hEq : L - (j - i) = i := by omega
      have hjeq : j = L := by omega
      rw [if_pos hc, hEq, heq, hjeq]
      exact hL
    · rw [if_neg hc]
      have hEq : L - (j - i) + (j - i) = L := by omega
      rw [hEq]
      exact hL
  · intro k hk
    dsimp only
    by_cases hc : k ≤ i
    · by_cases hc1 : k + 1 ≤ i
      · rw [if_pos hc, if_pos hc1]
        exact hstep k (by omega)
      · have hki : k = i := by omega
        subst hki
        rw [if_pos hc, if_neg hc1]
        have : k + 1 + (j - k) = j + 1 := by omega
        rw [this]
        rw [heq]
        exact hstep j (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬ (k + 1 ≤ i))]
      have : k + 1 + (j - i) = (k + (j - i)) + 1 := by omega
      rw [this]
      exact hstep _ (by omega)


/-- The endpoints of an edge are vertices. -/
theorem adj_right_mem_extremePoints {P : Set E} {a b : E} (h : Adj P a b) :
    b ∈ Set.extremePoints ℝ P := by
  have hb : b ∈ Set.extremePoints ℝ (segment ℝ a b) := by
    refine ⟨right_mem_segment ℝ a b, ?_⟩
    rintro x hx y hy ⟨p, q, hp, hq, hpq, hxy⟩
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h.1)
    rw [segment_eq_image'] at hx hy
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have hb' : b = a + (1:ℝ) • (b - a) := by module
    have hcomb : p • (a + s • (b - a)) + q • (a + t • (b - a))
        = a + (p * s + q * t) • (b - a) := by
      calc p • (a + s • (b - a)) + q • (a + t • (b - a))
          = (p + q) • a + (p * s + q * t) • (b - a) := by module
        _ = a + (p * s + q * t) • (b - a) := by rw [hpq]; module
    have hb2 : a + (p * s + q * t) • (b - a) = b := by rw [← hcomb]; exact hxy
    have hco : p * s + q * t = 1 := by
      have h3 : ((p * s + q * t) - 1) • (b - a) = 0 := by
        have e1 : ((p * s + q * t) - 1) • (b - a)
            = (a + (p * s + q * t) • (b - a)) - (a + (1:ℝ) • (b - a)) := by module
        rw [e1, hb2, ← hb', sub_self]
      rcases smul_eq_zero.mp h3 with h4 | h4
      · linarith [sub_eq_zero.mp h4]
      · exact absurd h4 hba
    have hs1 : s = 1 := by
      have h5 : p * s + q * t ≤ p * 1 + q * 1 := by
        have := hs.2; have := ht.2
        nlinarith
      nlinarith [hs.2, ht.2, hs.1, ht.1]
    rw [hs1]
    module
  have := h.2.extremePoints_eq (𝕜 := ℝ)
  rw [this] at hb
  exact hb.2

theorem reach_one_of_adj (P : Set E) {u v : E} (h : Adj P u v) : Reach P 1 u v := by
  classical
  refine ⟨fun i => if i = 0 then u else v, by simp, by simp, ?_⟩
  intro i hi
  have : i = 0 := by omega
  subst this
  exact Or.inr (by simpa using h)

theorem reach_trans (P : Set E) {L₁ L₂ : ℕ} {u x v : E}
    (h₁ : Reach P L₁ u x) (h₂ : Reach P L₂ x v) : Reach P (L₁ + L₂) u v := by
  classical
  obtain ⟨w₁, a1, b1, s1⟩ := h₁
  obtain ⟨w₂, a2, b2, s2⟩ := h₂
  refine ⟨fun i => if i ≤ L₁ then w₁ i else w₂ (i - L₁), by simpa using a1, ?_, ?_⟩
  · dsimp only
    by_cases hc : L₁ + L₂ ≤ L₁
    · have hz : L₂ = 0 := by omega
      subst hz
      rw [if_pos hc]
      simpa using b1.trans (by rw [← a2, ← b2])
    · rw [if_neg hc]
      have : L₁ + L₂ - L₁ = L₂ := by omega
      rw [this]; exact b2
  · intro i hi
    dsimp only
    by_cases hc : i ≤ L₁
    · by_cases hc1 : i + 1 ≤ L₁
      · rw [if_pos hc, if_pos hc1]; exact s1 i (by omega)
      · have hiL : i = L₁ := by omega
        subst hiL
        rw [if_pos hc, if_neg hc1]
        have : i + 1 - i = 1 := by omega
        rw [this, b1, ← a2]
        exact s2 0 (by omega)
    · rw [if_neg hc, if_neg (by omega : ¬ (i + 1 ≤ L₁))]
      have : i + 1 - L₁ = (i - L₁) + 1 := by omega
      rw [this]
      exact s2 _ (by omega)

theorem reach_tail (P : Set E) {L : ℕ} {v : E} {w : ℕ → E}
    (hL : w L = v) (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1)))
    {k : ℕ} (hk : k ≤ L) : Reach P (L - k) (w k) v := by
  refine ⟨fun i => w (i + k), by simp, ?_, ?_⟩
  · dsimp only
    have hEq : L - k + k = L := by omega
    rw [hEq]; exact hL
  · intro i hi
    dsimp only
    have hEq : i + 1 + k = (i + k) + 1 := by omega
    rw [hEq]
    exact hstep _ (by omega)


/-- **A connected vertex-edge graph of minimum degree two has diameter at most
`|V| - 2`.**  On a shortest walk all vertices are distinct, so its length is at most
`|V| - 1`; and a walk of that length visits every vertex, so the second neighbour of
its starting point is a later vertex on the walk and provides a shortcut. -/
theorem diam_le_card_sub_two (P : Set E) (V : Finset E)
    (hextV : ∀ z ∈ Set.extremePoints ℝ P, z ∈ V)
    (hconn : ∀ u ∈ V, ∀ v ∈ V, ∃ L, Reach P L u v)
    (hdeg : ∀ u ∈ V, ∃ w₁ ∈ V, ∃ w₂ ∈ V, w₁ ≠ w₂ ∧ Adj P u w₁ ∧ Adj P u w₂) :
    DiamLE P (V.card - 2) := by
  classical
  refine diamLE_of_reach P _ (fun u hu v hv => ?_)
  have huV := hextV u hu
  have hvV := hextV v hv
  have hex : ∃ L, Reach P L u v := hconn u huV v hvV
  have hfind : Reach P (Nat.find hex) u v := Nat.find_spec hex
  have hmin : ∀ L, L < Nat.find hex → ¬ Reach P L u v := fun L hL => Nat.find_min hex hL
  set L₀ := Nat.find hex with hL₀def
  obtain ⟨w, h0, hLw, hstep⟩ := hfind
  have hmem : ∀ i, i ≤ L₀ → w i ∈ V := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact huV
    | succ m ih =>
        intro hm
        rcases hstep m (by omega) with he | hadj
        · rw [← he]; exact ih (by omega)
        · exact hextV _ (adj_right_mem_extremePoints hadj)
  have hinj : ∀ i, i ≤ L₀ → ∀ j, j ≤ L₀ → w i = w j → i = j := by
    intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin _ (by omega) (reach_of_repeat P L₀ u v w h0 hLw hstep hlt hj hij)
    · exact hmin _ (by omega) (reach_of_repeat P L₀ u v w h0 hLw hstep hlt hi hij.symm)
  -- the walk injects into the vertex set
  have hcard : L₀ + 1 ≤ V.card := by
    have himg : ((Finset.range (L₀ + 1)).image w) ⊆ V := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hmem i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi)
    have hcardimg : ((Finset.range (L₀ + 1)).image w).card = L₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) j
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj) hij
    calc L₀ + 1 = ((Finset.range (L₀ + 1)).image w).card := hcardimg.symm
      _ ≤ V.card := Finset.card_le_card himg
  -- three distinct vertices exist
  obtain ⟨y₁, hy₁V, y₂, hy₂V, hy12, hadj1, hadj2⟩ := hdeg u huV
  have hy1u : y₁ ≠ u := fun h => hadj1.1 h.symm
  have hy2u : y₂ ≠ u := fun h => hadj2.1 h.symm
  have hcard3 : 3 ≤ V.card := by
    have hsub : ({u, y₁, y₂} : Finset E) ⊆ V := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact huV
      · exact hy₁V
      · exact hy₂V
    have : ({u, y₁, y₂} : Finset E).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hy1u, Ne.symm hy2u]),
        Finset.card_insert_of_notMem (by simp [hy12]), Finset.card_singleton]
    calc (3:ℕ) = ({u, y₁, y₂} : Finset E).card := this.symm
      _ ≤ V.card := Finset.card_le_card hsub
  by_cases hshort : L₀ ≤ V.card - 2
  · exact ⟨L₀, hshort, ⟨w, h0, hLw, hstep⟩⟩
  -- otherwise the walk visits every vertex and the second neighbour is a shortcut
  exfalso
  have hL₀eq : L₀ = V.card - 1 := by omega
  have hsurj : ∀ y ∈ V, ∃ k ≤ L₀, w k = y := by
    intro y hyV
    by_contra hcon
    push_neg at hcon
    have hsub : (insert y ((Finset.range (L₀ + 1)).image w)) ⊆ V := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz'
      · exact hyV
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz'
        exact hmem i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi)
    have hnotmem : y ∉ ((Finset.range (L₀ + 1)).image w) := by
      intro hy
      obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
      exact absurd hiy (hcon i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi))
    have hcardimg : ((Finset.range (L₀ + 1)).image w).card = L₀ + 1 := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj hij
      exact hinj i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi) j
        (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj) hij
    have : L₀ + 2 ≤ V.card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnotmem, hcardimg] at this
      omega
    omega
  -- pick a neighbour of `u` different from the walk's first step
  have hL1 : 1 ≤ L₀ := by omega
  obtain ⟨y, hyV, hyadj, hy1⟩ : ∃ y ∈ V, Adj P u y ∧ y ≠ w 1 := by
    by_cases hc : y₁ = w 1
    · exact ⟨y₂, hy₂V, hadj2, by rw [← hc]; exact hy12.symm⟩
    · exact ⟨y₁, hy₁V, hadj1, hc⟩
  obtain ⟨k, hk, hky⟩ := hsurj y hyV
  have hk0 : k ≠ 0 := by
    intro h; rw [h, h0] at hky; exact hyadj.1 hky
  have hk1 : k ≠ 1 := by intro h; rw [h] at hky; exact hy1 hky.symm
  have hk2 : 2 ≤ k := by omega
  have hshort2 : Reach P (1 + (L₀ - k)) u v :=
    reach_trans P (reach_one_of_adj P hyadj) (hky ▸ reach_tail P hLw hstep hk)
  exact hmin _ (by omega) hshort2

end HirschWalk

open scoped RealInnerProductSpace
open Hirsch LinearOptimization

namespace HirschBridge

variable {d n : ℕ}

/-- The mission's H-polytope, read as a Bertsimas--Tsitsiklis constraint system. -/
def constrOf (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Fin n → LinearConstraint d :=
  fun i => ⟨fun j => a i j, b i, .le⟩

/-- The type synonym `EuclideanSpace ℝ (Fin d) = WithLp 2 (Fin d → ℝ)` as a linear
equivalence, used to move between the mission's model and the B&T one. -/
noncomputable def eqv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin d → ℝ)

theorem eqv_apply (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) : eqv d x j = x j := rfl

theorem inner_eq_dotProduct (a x : EuclideanSpace ℝ (Fin d)) :
    ⟪a, x⟫ = (fun j => a j) ⬝ᵥ (eqv d x) := by
  simp [PiLp.inner_apply, dotProduct, eqv_apply, mul_comm]

theorem image_hpoly (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (eqv d) '' (Hpoly a b) = constraintSet (constrOf a b) := by
  apply Set.eq_of_subset_of_subset
  · rintro y ⟨x, hx, rfl⟩ i
    have := hx i
    simpa [constrOf, LinearConstraint.IsSatisfiedAt, ← inner_eq_dotProduct] using this
  · intro y hy
    refine ⟨(eqv d).symm y, fun i => ?_, (eqv d).apply_symm_apply y⟩
    have := hy i
    simp only [constrOf, LinearConstraint.IsSatisfiedAt] at this
    have hrw : ⟪a i, (eqv d).symm y⟫ = (fun j => a i j) ⬝ᵥ y := by
      rw [inner_eq_dotProduct, (eqv d).apply_symm_apply]
    rw [hrw]
    exact this

/-- **The vertex set of an H-polytope is finite.**  Transported from the platform's
`LinearOptimization` layer: extreme points of a constraint system are exactly its
basic feasible solutions (B&T Thm. 2.3), and there are only finitely many of those
(B&T Cor. 2.1). -/
theorem extremePoints_finite (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    (Set.extremePoints ℝ (Hpoly a b)).Finite := by
  classical
  rcases Set.eq_empty_or_nonempty (Set.extremePoints ℝ (Hpoly a b)) with h | ⟨x0, hx0⟩
  · rw [h]; exact Set.finite_empty
  have hne : (Hpoly a b).Nonempty := ⟨x0, hx0.1⟩
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]
    exact ⟨eqv d x0, x0, hx0.1, rfl⟩
  -- extreme points of the constraint system are basic feasible solutions
  have hsub : Set.extremePoints ℝ (constraintSet (constrOf a b))
      ⊆ {x | IsBasicFeasibleSolution (constrOf a b) x} := by
    intro x hx
    exact ((lp_vertex_extreme_bfs_equiv (constrOf a b) x hCne hx.1).out 1 2).mp hx
  have hfin : (Set.extremePoints ℝ (constraintSet (constrOf a b))).Finite :=
    Set.Finite.subset (lp_basic_solutions_finite (constrOf a b)).2 hsub
  -- transport back along the linear equivalence
  have himg : (eqv d) '' (Set.extremePoints ℝ (Hpoly a b))
      = Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [image_extremePoints (eqv d) (Hpoly a b), image_hpoly a b]
  have : ((eqv d) '' (Set.extremePoints ℝ (Hpoly a b))).Finite := himg ▸ hfin
  exact Set.Finite.of_finite_image this ((eqv d).injective.injOn)


/-- An H-polytope is closed: it is an intersection of closed half-spaces. -/
theorem hpoly_closed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  have : Hpoly a b = ⋂ i, {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} := by
    ext x; simp [Hpoly, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

theorem hpoly_compact (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) : IsCompact (Hpoly a b) :=
  Metric.isCompact_of_isClosed_isBounded (hpoly_closed a b) hbd

/-- **Minkowski's theorem for H-polytopes.**  A bounded H-polytope is the convex hull
of its finitely many vertices.  Krein--Milman gives the closure of the hull; the hull
of a finite set is already compact, hence closed, so the closure is redundant. -/
theorem hpoly_eq_convexHull (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Hpoly a b = convexHull ℝ (Set.extremePoints ℝ (Hpoly a b)) := by
  have hcomp := hpoly_compact a b hbd
  have hconv : Convex ℝ (Hpoly a b) := by
    intro x hx y hy s t hs ht hst i
    have h1 := hx i
    have h2 := hy i
    have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hexp]
    have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
    have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
    have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
    linarith
  have hcl := closure_convexHull_extremePoints hcomp hconv
  have hfin := extremePoints_finite a b
  have hhullcomp : IsCompact (convexHull ℝ (Set.extremePoints ℝ (Hpoly a b))) :=
    hfin.isCompact_convexHull ℝ
  calc Hpoly a b = closure (convexHull ℝ (Set.extremePoints ℝ (Hpoly a b))) := hcl.symm
    _ = convexHull ℝ (Set.extremePoints ℝ (Hpoly a b)) := hhullcomp.isClosed.closure_eq


/-- **Every vertex is exposed by a strictly separating functional.**  Transported
from B&T Thm. 2.3: an extreme point of a constraint system is a *vertex* in the
book's sense, i.e. the unique minimiser of some linear cost. -/
theorem exists_strict_functional (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ g : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ, ∀ y ∈ Hpoly a b, y ≠ u → g u < g y := by
  classical
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]; exact ⟨eqv d u, u, hu.1, rfl⟩
  have humem : eqv d u ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨u, hu.1, rfl⟩
  have huext : eqv d u ∈ Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [← image_hpoly a b, ← image_extremePoints (eqv d) (Hpoly a b)]
    exact ⟨u, hu, rfl⟩
  obtain ⟨-, c, hc⟩ :=
    ((lp_vertex_extreme_bfs_equiv (constrOf a b) (eqv d u) hCne humem).out 1 0).mp huext
  let g0 : (Fin d → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y => c ⬝ᵥ y
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun r x => by simp [dotProduct_smul] }
  refine ⟨g0.comp (eqv d).toLinearMap, ?_⟩
  intro y hy hyu
  have hymem : eqv d y ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨y, hy, rfl⟩
  exact hc _ hymem (fun h => hyu ((eqv d).injective h))


/-- **Every vertex has `d` linearly independent active constraints** (B&T Thm. 2.3 +
Def. 2.9).  In particular their normals are nonzero. -/
theorem exists_active_basis (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ s : Finset (Fin n), s.card = d ∧ (∀ i ∈ s, ⟪a i, u⟫ = b i) ∧ (∀ i ∈ s, a i ≠ 0) := by
  classical
  have hCne : (constraintSet (constrOf a b)).Nonempty := by
    rw [← image_hpoly a b]; exact ⟨eqv d u, u, hu.1, rfl⟩
  have humem : eqv d u ∈ constraintSet (constrOf a b) := by
    rw [← image_hpoly a b]; exact ⟨u, hu.1, rfl⟩
  have huext : eqv d u ∈ Set.extremePoints ℝ (constraintSet (constrOf a b)) := by
    rw [← image_hpoly a b, ← image_extremePoints (eqv d) (Hpoly a b)]
    exact ⟨u, hu, rfl⟩
  obtain ⟨⟨-, s, hcard, hact, hindep⟩, -⟩ :=
    ((lp_vertex_extreme_bfs_equiv (constrOf a b) (eqv d u) hCne humem).out 1 2).mp huext
  refine ⟨s, hcard, ?_, ?_⟩
  · intro i hi
    have := hact i hi
    simp only [LinearConstraint.IsActiveAt, constrOf] at this
    rw [inner_eq_dotProduct]
    exact this
  · intro i hi
    have hz := hindep.ne_zero (⟨i, hi⟩ : {x // x ∈ s})
    intro hcon
    apply hz
    simp only [constrOf]
    funext j
    have : a i j = 0 := by rw [hcon]; rfl
    simpa using this

end HirschBridge

open Hirsch HirschLib HirschWalk

namespace HirschPlane

/-- Descending along improving edges reaches the unique minimiser of `c`. -/
theorem reach_of_improving (V : Finset E2) (P : Set E2)
    (himp : ∀ u ∈ V, ∀ c : E2 →ₗ[ℝ] ℝ, (∃ z ∈ V, c z < c u) →
      ∃ w ∈ V, c w < c u ∧ Adj P u w)
    (c : E2 →ₗ[ℝ] ℝ) (v : E2) (hv : v ∈ V) (hcv : ∀ y ∈ V, y ≠ v → c v < c y) :
    ∀ u ∈ V, ∃ L, Reach P L u v := by
  classical
  have key : ∀ (m : ℕ) (u : E2), u ∈ V →
      (V.filter (fun z => c z < c u)).card = m → ∃ L, Reach P L u v := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u huV hcard
      by_cases huv : u = v
      · exact ⟨0, huv ▸ reach_zero P u⟩
      · obtain ⟨w, hwV, hwc, hadj⟩ := himp u huV c ⟨v, hv, hcv u huV huv⟩
        have hsub : V.filter (fun z => c z < c w) ⊆ V.filter (fun z => c z < c u) := by
          intro z hz
          obtain ⟨hzV, hzc⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨hzV, lt_trans hzc hwc⟩
        have hss : V.filter (fun z => c z < c w) ⊂ V.filter (fun z => c z < c u) := by
          refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨w, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨hwV, hwc⟩
          · intro hcon
            exact absurd (Finset.mem_filter.mp hcon).2 (lt_irrefl _)
        have hlt : (V.filter (fun z => c z < c w)).card < m :=
          hcard ▸ Finset.card_lt_card hss
        obtain ⟨L, hL⟩ := ih _ hlt w hwV rfl
        exact ⟨1 + L, reach_trans P (reach_one_of_adj P hadj) hL⟩
  intro u huV
  exact key _ u huV rfl

/-- **The vertex-edge graph of a planar polytope is connected and has minimum degree
two**, hence diameter at most `|V| - 2`. -/
theorem diam_le_card_sub_two_plane (V : Finset E2) (P : Set E2)
    (hP : P = convexHull ℝ (V : Set E2))
    (hVext : ∀ z ∈ V, z ∈ Set.extremePoints ℝ P)
    (hextV : ∀ z ∈ Set.extremePoints ℝ P, z ∈ V)
    (hnl : ∀ (q : E2 →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, q z = t) → q = 0)
    (hvert : ∀ u ∈ V, ∃ g : E2 →ₗ[ℝ] ℝ, ∀ z ∈ V, z ≠ u → g u < g z) :
    DiamLE P (V.card - 2) := by
  classical
  have himp : ∀ u ∈ V, ∀ c : E2 →ₗ[ℝ] ℝ, (∃ z ∈ V, c z < c u) →
      ∃ w ∈ V, c w < c u ∧ Adj P u w := by
    intro u huV c hex
    obtain ⟨g, hg⟩ := hvert u huV
    exact improving_edge_plane V P hP hVext u huV g hg c hex
  refine diam_le_card_sub_two P V hextV ?_ ?_
  · intro u huV v hvV
    obtain ⟨c, hc⟩ := hvert v hvV
    exact reach_of_improving V P himp c v hvV (fun y hyV hyv => hc y hyV hyv) u huV
  · intro u huV
    obtain ⟨g, hg⟩ := hvert u huV
    exact two_neighbours_plane V P hP hVext hnl u huV g hg

end HirschPlane

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschBridge

namespace HirschCount

variable {n : ℕ}

/-- The functional `⟪a, ·⟫`. -/
noncomputable def innerFun (v : E2) : E2 →ₗ[ℝ] ℝ := (innerSL ℝ v).toLinearMap

theorem innerFun_apply (v x : E2) : innerFun v x = ⟪v, x⟫ := rfl

theorem innerFun_ne_zero {v : E2} (hv : v ≠ 0) : innerFun v ≠ 0 := by
  intro h
  have h1 : innerFun v v = 0 := by rw [h]; rfl
  rw [innerFun_apply, real_inner_self_eq_norm_sq] at h1
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact hv (norm_eq_zero.mp this)

/-- **At most two vertices are tight for one inequality.** -/
theorem tight_card_le_two (a : Fin n → E2) (b : Fin n → ℝ) (V : Finset E2)
    (hV : ∀ z ∈ V, z ∈ Set.extremePoints ℝ (Hpoly a b)) (i : Fin n) (hai : a i ≠ 0) :
    (V.filter (fun z => ⟪a i, z⟫ = b i)).card ≤ 2 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hcon
  have hrk : Module.finrank ℝ E2 ≤ 2 := by simp
  refine card_le_two_on_level hrk (Hpoly a b) (innerFun (a i)) (innerFun_ne_zero hai) (b i)
    (hV x (Finset.mem_filter.mp hx).1) (hV y (Finset.mem_filter.mp hy).1)
    (hV z (Finset.mem_filter.mp hz).1)
    (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hz).2
    hxy hxz hyz

/-- **A planar polytope has at most as many vertices as inequalities.**  Each vertex
carries two linearly independent active constraints, and each constraint is tight at
at most two vertices, so `2m ≤ 2n`. -/
theorem card_le_of_vertices (a : Fin n → E2) (b : Fin n → ℝ) (V : Finset E2)
    (hV : ∀ z ∈ V, z ∈ Set.extremePoints ℝ (Hpoly a b)) : V.card ≤ n := by
  classical
  choose s hcard hact hne using fun (u : E2) (hu : u ∈ V) =>
    exists_active_basis a b (hV u hu)
  set D : Finset (E2 × Fin n) :=
    V.attach.biUnion (fun u => (s u.1 u.2).image (fun i => (u.1, i))) with hD
  have hDcard : D.card = 2 * V.card := by
    rw [hD, Finset.card_biUnion]
    · have : ∀ u ∈ V.attach, ((s u.1 u.2).image (fun i => (u.1, i))).card = 2 := by
        intro u _
        rw [Finset.card_image_of_injective _ (fun i j hij => by simpa using hij), hcard]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_attach, smul_eq_mul,
        mul_comm]
    · intro u _ v _ huv
      simp only [Finset.disjoint_left, Finset.mem_image]
      rintro p ⟨i, -, rfl⟩ ⟨j, -, hj⟩
      exact huv (Subtype.ext (congrArg Prod.fst hj).symm)
  have hfib : ∀ i : Fin n, (D.filter (fun p => p.2 = i)).card ≤ 2 := by
    intro i
    by_cases hai : a i = 0
    · -- a zero normal is never part of an independent active set
      have : D.filter (fun p => p.2 = i) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem ?_
        intro p hp
        obtain ⟨hpD, hpi⟩ := Finset.mem_filter.mp hp
        rw [hD] at hpD
        obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp hpD
        obtain ⟨j, hjs, hj⟩ := Finset.mem_image.mp hu
        have : j = i := by rw [← hpi, ← hj]
        subst this
        exact hne u.1 u.2 j hjs hai
      rw [this]; simp
    · refine le_trans (Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_)
        (tight_card_le_two a b V hV i hai)
      · intro p hp
        obtain ⟨hpD, hpi⟩ := Finset.mem_filter.mp hp
        rw [hD] at hpD
        obtain ⟨u, -, hu⟩ := Finset.mem_biUnion.mp hpD
        obtain ⟨j, hjs, hj⟩ := Finset.mem_image.mp hu
        have hji : j = i := by rw [← hpi, ← hj]
        subst hji
        have hp1 : p.1 = u.1 := by rw [← hj]
        dsimp only
        rw [Finset.mem_coe, hp1]
        exact Finset.mem_filter.mpr ⟨u.2, hact u.1 u.2 j hjs⟩
      · intro p hp q hq hpq
        obtain ⟨-, hpi⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hqi⟩ := Finset.mem_filter.mp hq
        exact Prod.ext hpq (by rw [hpi, hqi])
  have hsplit : D.card = ∑ i : Fin n, (D.filter (fun p => p.2 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_univ p.2)
  have : D.card ≤ 2 * n := by
    rw [hsplit]
    calc ∑ i : Fin n, (D.filter (fun p => p.2 = i)).card ≤ ∑ _i : Fin n, 2 :=
          Finset.sum_le_sum fun i _ => hfib i
      _ = 2 * n := by simp [mul_comm]
  omega

end HirschCount

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschBridge HirschPlane HirschCount

namespace HirschDim2

theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hB : B ≤ B') (h : DiamLE P B) : DiamLE P B' := by
  refine diamLE_of_reach P B' (fun u hu v hv => ?_)
  exact ⟨B, hB, h u hu v hv⟩

theorem dimension_two (n : ℕ) (a : Fin n → E2) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 2) := by
  classical
  set V : Finset E2 := (extremePoints_finite a b).toFinset with hVdef
  have hmemV : ∀ z, z ∈ V ↔ z ∈ Set.extremePoints ℝ (Hpoly a b) := by
    intro z; rw [hVdef]; exact Set.Finite.mem_toFinset _
  have hcoeV : (V : Set E2) = Set.extremePoints ℝ (Hpoly a b) := by
    ext z; rw [Finset.mem_coe, hmemV]
  have hP : Hpoly a b = convexHull ℝ (V : Set E2) := by
    rw [hcoeV]; exact hpoly_eq_convexHull a b hbd
  have hn3 : 3 ≤ n := by
    have := succ_le_of_bounded (d := 2) (by omega) a b hne hbd
    omega
  rcases Nat.lt_or_ge 1 V.card with hcard2 | hcard1
  swap
  · refine diamLE_of_subsingleton _ _ (fun u hu v hv => ?_)
    have hu' : u ∈ V := (hmemV u).mpr hu
    have hv' : v ∈ V := (hmemV v).mpr hv
    exact Finset.card_le_one.mp hcard1 u hu' v hv'
  rcases Nat.lt_or_ge V.card 3 with hcard | hcard3
  · -- exactly two vertices: the polytope is a single edge
    have hc2 : V.card = 2 := by omega
    obtain ⟨u, v, huv, hVeq⟩ := Finset.card_eq_two.mp hc2
    refine diamLE_of_adj _ _ (by omega) (fun x hx y hy => ?_)
    have hxV : x ∈ V := (hmemV x).mpr hx
    have hyV : y ∈ V := (hmemV y).mpr hy
    rw [hVeq] at hxV hyV
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxV hyV
    have hseg : Hpoly a b = segment ℝ u v := by
      rw [hP, hVeq]
      simp [convexHull_pair]
    have hadj : ∀ p q : E2, p ≠ q → (p = u ∨ p = v) → (q = u ∨ q = v) → Adj (Hpoly a b) p q := by
      intro p q hpq hp hq
      refine ⟨hpq, ?_⟩
      have : segment ℝ p q = Hpoly a b := by
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
        · exact absurd rfl hpq
        · exact hseg.symm
        · rw [segment_symm]; exact hseg.symm
        · exact absurd rfl hpq
      rw [this]
      exact IsExtreme.refl ℝ _
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr (hadj x y hxy hxV hyV)
  · -- at least three vertices: the planar graph argument
    have hnl : ∀ (q : E2 →ₗ[ℝ] ℝ) (t : ℝ), (∀ z ∈ V, q z = t) → q = 0 := by
      intro q t hq
      by_contra hq0
      obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < V.card)
      have hrk : Module.finrank ℝ E2 ≤ 2 := by simp
      exact card_le_two_on_level hrk (Hpoly a b) q hq0 t
        ((hmemV x).mp hx) ((hmemV y).mp hy) ((hmemV z).mp hz)
        (hq x hx) (hq y hy) (hq z hz) hxy hxz hyz
    have hvert : ∀ u ∈ V, ∃ g : E2 →ₗ[ℝ] ℝ, ∀ z ∈ V, z ≠ u → g u < g z := by
      intro u huV
      obtain ⟨g, hg⟩ := exists_strict_functional a b ((hmemV u).mp huV)
      exact ⟨g, fun z hzV hzu => hg z (((hmemV z).mp hzV).1) hzu⟩
    have hmain := diam_le_card_sub_two_plane V (Hpoly a b) hP
      (fun z hz => (hmemV z).mp hz) (fun z hz => (hmemV z).mpr hz) hnl hvert
    have hle : V.card ≤ n := card_le_of_vertices a b V (fun z hz => (hmemV z).mp hz)
    exact diamLE_mono _ (by omega) hmain

end HirschDim2


open HirschDim2

theorem solution (n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin 2)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - 2) :=
  dimension_two n a b hne hbd
