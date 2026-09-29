-- Prove2me | solution 1 for Hirsch.todd_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T10:54:50.489671+00:00
-- url     : https://prove2.me/submissions/19160d40-cb1e-44c4-b65c-f32134c5e161

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ActiveConstraints
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Theorems.Thm_Hirsch_graph_connected_general
import Theorems.Thm_Hirsch_plane_bound_general

open scoped RealInnerProductSpace
open Hirsch LinearOptimization

open scoped RealInnerProductSpace
open Hirsch

namespace HirschLib



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

end HirschWalk

open Hirsch HirschLib

namespace HirschFace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The minimising face of a linear functional over a convex set is an extreme subset. -/
theorem exposed_isExtreme (P : Set E) (f : E →ₗ[ℝ] ℝ) (t : ℝ)
    (hmin : ∀ x ∈ P, t ≤ f x) : IsExtreme ℝ P {x | x ∈ P ∧ f x = t} := by
  constructor
  · exact fun x hx => hx.1
  · rintro x₁ hx₁ x₂ hx₂ x ⟨hxP, hxt⟩ ⟨p, q, hp, hq, hpq, hx⟩
    have hc : f x = p * f x₁ + q * f x₂ := by
      rw [← hx, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have h1 := hmin _ hx₁
    have h2 := hmin _ hx₂
    have h3 : p * f x₁ + q * f x₂ = t := by rw [← hc, hxt]
    have key : p * (f x₁ - t) + q * (f x₂ - t) = 0 := by linear_combination h3 - t * hpq
    have hz1 : 0 ≤ p * (f x₁ - t) := mul_nonneg hp.le (by linarith)
    have hz2 : 0 ≤ q * (f x₂ - t) := mul_nonneg hq.le (by linarith)
    refine ⟨hx₁, ?_⟩
    have : p * (f x₁ - t) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hp)
    · linarith

end HirschFace

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


/-- The active basis at a vertex, with the linear independence of its normals. -/
theorem exists_active_basis_indep (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ s : Finset (Fin n), s.card = d ∧ (∀ i ∈ s, ⟪a i, u⟫ = b i) ∧
      LinearIndependent ℝ (fun i : s => a i.1) := by
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
  · have h1 : LinearIndependent ℝ (fun i : s => (constrOf a b i.1).a) := hindep
    have h2 := h1.map' (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap
      (LinearMap.ker_eq_bot_of_injective (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.injective)
    exact h2

end HirschBridge

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschBridge HirschFace LinearOptimization

namespace HirschSimple

variable {d n : ℕ}

/-- The set of inequalities tight at a point. -/
noncomputable def tightSet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

/-- **A point with `d` linearly independent tight inequalities is a vertex.**  Holds for
any H-polyhedron, bounded or not: on an open segment through such a point every tight
inequality stays tight at both ends, so the difference is orthogonal to a basis. -/
theorem extreme_of_indep_tight (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Hpoly a b) {s : Finset (Fin n)}
    (hst : ∀ i ∈ s, ⟪a i, x⟫ = b i) (hind : LinearIndependent ℝ (fun i : s => a i.1))
    (hcard : s.card = d) : x ∈ Set.extremePoints ℝ (Hpoly a b) := by
  classical
  have hspan : Submodule.span ℝ (Set.range (fun i : s => a i.1)) = ⊤ := by
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i.1))) = d := by
      rw [finrank_span_eq_card hind]; simp [hcard]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfr]; simp)
  refine ⟨hx, ?_⟩
  rintro x₁ hx₁ x₂ hx₂ ⟨p, q, hp, hq, hpq, hsum⟩
  -- every tight inequality is tight at both endpoints
  have htight : ∀ i ∈ s, ⟪a i, x₁⟫ = b i := by
    intro i hi
    have h1 : ⟪a i, x₁⟫ ≤ b i := hx₁ i
    have h2 : ⟪a i, x₂⟫ ≤ b i := hx₂ i
    have h3 : p * ⟪a i, x₁⟫ + q * ⟪a i, x₂⟫ = b i := by
      have := hst i hi
      rw [← this, ← hsum, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hz : p * (b i - ⟪a i, x₁⟫) + q * (b i - ⟪a i, x₂⟫) = 0 := by
      linear_combination (b i) * hpq - h3
    have hn1 : 0 ≤ p * (b i - ⟪a i, x₁⟫) := mul_nonneg hp.le (by linarith)
    have hn2 : 0 ≤ q * (b i - ⟪a i, x₂⟫) := mul_nonneg hq.le (by linarith)
    have : p * (b i - ⟪a i, x₁⟫) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hp)
    · linarith
  -- so the difference is orthogonal to everything
  have hzero : ∀ w : EuclideanSpace ℝ (Fin d), ⟪w, x₁ - x⟫ = 0 := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Set.range (fun i : s => a i.1)) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        show ⟪a i.1, x₁ - x⟫ = 0
        rw [inner_sub_right, htight i.1 i.2, hst i.1 i.2, sub_self]
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz]; ring
    | smul c y _ hy => rw [real_inner_smul_left, hy]; ring
  have := hzero (x₁ - x)
  rw [real_inner_self_eq_norm_sq] at this
  have hn : ‖x₁ - x‖ = 0 := by nlinarith [norm_nonneg (x₁ - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Making the inequalities outside `F` vacuous. -/
noncomputable def relaxA (a : Fin n → EuclideanSpace ℝ (Fin d)) (F : Finset (Fin n)) :
    Fin n → EuclideanSpace ℝ (Fin d) := fun j => if j ∈ F then a j else 0

noncomputable def relaxB (b : Fin n → ℝ) (F : Finset (Fin n)) : Fin n → ℝ :=
  fun j => if j ∈ F then b j else 1

theorem subset_relax (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) : Hpoly a b ⊆ Hpoly (relaxA a F) (relaxB b F) := by
  intro x hx j
  by_cases hj : j ∈ F
  · simp only [relaxA, relaxB, if_pos hj]; exact hx j
  · simp only [relaxA, relaxB, if_neg hj]
    simp

theorem tightSet_relax (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin d)) :
    tightSet (relaxA a F) (relaxB b F) x = tightSet a b x ∩ F := by
  ext j
  simp only [tightSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
    relaxA, relaxB]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp [hj]

theorem relaxA_of_mem (a : Fin n → EuclideanSpace ℝ (Fin d)) (F : Finset (Fin n))
    {j : Fin n} (hj : j ∈ F) : relaxA a F j = a j := by simp [relaxA, hj]

theorem relaxB_of_mem (b : Fin n → ℝ) (F : Finset (Fin n)) {j : Fin n} (hj : j ∈ F) :
    relaxB b F j = b j := by simp [relaxB, hj]

end HirschSimple

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace

namespace HirschFacet

variable {d n m : ℕ}

/-- Every `m`-dimensional subspace of `ℝ^d` is the range of a linear isometric
embedding of `ℝ^m`. -/
theorem exists_chart (K : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (m : ℕ)
    (hK : Module.finrank ℝ K = m) :
    ∃ ψ : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      Set.range ψ = (K : Set (EuclideanSpace ℝ (Fin d))) := by
  subst hK
  refine ⟨K.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ K).repr.symm.toLinearIsometry, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩; exact ((stdOrthonormalBasis ℝ K).repr.symm y).2
  · intro hz
    exact ⟨(stdOrthonormalBasis ℝ K).repr ⟨z, hz⟩, by simp⟩

/-! ## Pulling the inequality data back along a chart -/

variable (ψ : EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))

/-- The normal vectors seen in the chart. -/
noncomputable def pullA (a : Fin n → EuclideanSpace ℝ (Fin d)) : Fin n → EuclideanSpace ℝ (Fin m) :=
  fun j => LinearMap.adjoint ψ.toLinearMap (a j)

/-- The right-hand sides seen in the chart based at `p`. -/
noncomputable def pullB (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : Fin n → ℝ :=
  fun j => b j - ⟪a j, p⟫

/-- The chart map: an affine isometric embedding of `ℝ^m` based at `p`. -/
noncomputable def chartMap (p : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d) :=
  fun y => p + ψ y

variable {ψ}

theorem pullA_inner (a : Fin n → EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (y : EuclideanSpace ℝ (Fin m)) : ⟪pullA ψ a j, y⟫ = ⟪a j, ψ y⟫ := by
  rw [pullA, LinearMap.adjoint_inner_left]
  rfl

theorem chartMap_inner (a : Fin n → EuclideanSpace ℝ (Fin d)) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin n) (y : EuclideanSpace ℝ (Fin m)) :
    ⟪a j, chartMap ψ p y⟫ = ⟪a j, p⟫ + ⟪pullA ψ a j, y⟫ := by
  rw [chartMap, inner_add_right, pullA_inner]

theorem chartMap_mem_iff (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin m)) :
    chartMap ψ p y ∈ Hpoly a b ↔ y ∈ Hpoly (pullA ψ a) (pullB a b p) := by
  constructor
  · intro h j
    have := h j
    rw [chartMap_inner] at this
    simp only [pullB]
    linarith
  · intro h j
    have := h j
    simp only [pullB] at this
    rw [chartMap_inner]
    linarith

theorem chartMap_injective (p : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (chartMap ψ p) := by
  intro y z h
  simp only [chartMap, add_right_inj] at h
  exact ψ.injective h

theorem chartMap_affine (p : EuclideanSpace ℝ (Fin d)) (s t : ℝ) (hst : s + t = 1)
    (y z : EuclideanSpace ℝ (Fin m)) :
    chartMap ψ p (s • y + t • z) = s • chartMap ψ p y + t • chartMap ψ p z := by
  have hp : s • p + t • p = p := by rw [← add_smul, hst, one_smul]
  simp only [chartMap, map_add, map_smul, smul_add]
  calc p + (s • ψ y + t • ψ z)
      = (s • p + t • p) + (s • ψ y + t • ψ z) := by rw [hp]
    _ = (s • p + s • ψ y) + (t • p + t • ψ z) := by abel

/-! ## Transporting faces, vertices and edges along the chart -/

theorem chartMap_openSegment (p : EuclideanSpace ℝ (Fin d)) (y z : EuclideanSpace ℝ (Fin m)) :
    openSegment ℝ (chartMap ψ p y) (chartMap ψ p z) = chartMap ψ p '' openSegment ℝ y z := by
  ext w
  constructor
  · rintro ⟨s, t, hs, ht, hst, hw⟩
    exact ⟨s • y + t • z, ⟨s, t, hs, ht, hst, rfl⟩,
      by rw [chartMap_affine p s t hst, hw]⟩
  · rintro ⟨w', ⟨s, t, hs, ht, hst, hw'⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [← chartMap_affine p s t hst, hw']⟩

theorem chartMap_segment (p : EuclideanSpace ℝ (Fin d)) (y z : EuclideanSpace ℝ (Fin m)) :
    segment ℝ (chartMap ψ p y) (chartMap ψ p z) = chartMap ψ p '' segment ℝ y z := by
  ext w
  constructor
  · rintro ⟨s, t, hs, ht, hst, hw⟩
    exact ⟨s • y + t • z, ⟨s, t, hs, ht, hst, rfl⟩,
      by rw [chartMap_affine p s t hst, hw]⟩
  · rintro ⟨w', ⟨s, t, hs, ht, hst, hw'⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [← chartMap_affine p s t hst, hw']⟩

theorem chartMap_isExtreme (p : EuclideanSpace ℝ (Fin d))
    {S T : Set (EuclideanSpace ℝ (Fin m))} (h : IsExtreme ℝ S T) :
    IsExtreme ℝ (chartMap ψ p '' S) (chartMap ψ p '' T) := by
  constructor
  · exact Set.image_mono h.1
  · rintro x1 ⟨u1, hu1, rfl⟩ x2 ⟨u2, hu2, rfl⟩ x ⟨w, hw, rfl⟩ hseg
    rw [chartMap_openSegment] at hseg
    obtain ⟨w', hw', hww'⟩ := hseg
    have : w = w' := chartMap_injective p hww'.symm
    subst this
    exact ⟨u1, h.2 hu1 hu2 hw hw', rfl⟩

theorem chartMap_extremePoints (p : EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin m))) (y : EuclideanSpace ℝ (Fin m)) :
    y ∈ Set.extremePoints ℝ S ↔ chartMap ψ p y ∈ Set.extremePoints ℝ (chartMap ψ p '' S) := by
  constructor
  · intro hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro x1 ⟨u1, hu1, rfl⟩ x2 ⟨u2, hu2, rfl⟩ hseg
    rw [chartMap_openSegment] at hseg
    obtain ⟨w, hw, hww⟩ := hseg
    have : y = w := chartMap_injective p hww.symm
    subst this
    exact congrArg _ (hy.2 hu1 hu2 hw)
  · intro hy
    obtain ⟨⟨y', hy', hyy⟩, hmax⟩ := hy
    have hyy' : y' = y := chartMap_injective p hyy
    rw [hyy'] at hy'
    refine ⟨hy', ?_⟩
    intro u1 hu1 u2 hu2 hseg
    have h2 : chartMap ψ p y ∈ openSegment ℝ (chartMap ψ p u1) (chartMap ψ p u2) := by
      rw [chartMap_openSegment]
      exact ⟨y, hseg, rfl⟩
    have := hmax ⟨u1, hu1, rfl⟩ ⟨u2, hu2, rfl⟩ h2
    exact chartMap_injective p this

theorem chartMap_adj (p : EuclideanSpace ℝ (Fin d)) {S : Set (EuclideanSpace ℝ (Fin m))}
    {y z : EuclideanSpace ℝ (Fin m)} (h : Adj S y z) :
    Adj (chartMap ψ p '' S) (chartMap ψ p y) (chartMap ψ p z) := by
  refine ⟨fun hc => h.1 (chartMap_injective p hc), ?_⟩
  rw [chartMap_segment]
  exact chartMap_isExtreme p h.2

/-- A walk in the chart is a walk in the image. -/
theorem chartMap_reach (p : EuclideanSpace ℝ (Fin d)) {S : Set (EuclideanSpace ℝ (Fin m))}
    {L : ℕ} {y z : EuclideanSpace ℝ (Fin m)} (h : Reach S L y z) :
    Reach (chartMap ψ p '' S) L (chartMap ψ p y) (chartMap ψ p z) := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => chartMap ψ p (w i), by dsimp only; rw [h0], by dsimp only; rw [hL],
    fun i hi => ?_⟩
  dsimp only
  rcases hstep i hi with he | hadj
  · exact Or.inl (by rw [he])
  · exact Or.inr (chartMap_adj p hadj)

/-- A walk inside an extreme subset is a walk in the ambient set. -/
theorem reach_of_extreme {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q : Set E}
    (hQ : IsExtreme ℝ P Q) {L : ℕ} {u v : E} (h : Reach Q L u v) : Reach P L u v := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨w, h0, hL, fun i hi => ?_⟩
  rcases hstep i hi with he | hadj
  · exact Or.inl he
  · exact Or.inr ⟨hadj.1, IsExtreme.trans hQ hadj.2⟩

/-! ## The facet cut out by one tight inequality -/

variable (ψ)

/-- The face of `Hpoly a b` on which the `i`-th inequality is tight. -/
def facet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}

variable {ψ}

theorem facet_isExtreme (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n) :
    IsExtreme ℝ (Hpoly a b) (facet a b i) := by
  have h := HirschFace.exposed_isExtreme (Hpoly a b) (-(innerSL ℝ (a i)).toLinearMap) (-b i)
    (fun x hx => by
      have := hx i
      simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe, neg_le_neg_iff]
      exact this)
  have hset : {x | x ∈ Hpoly a b ∧ (-(innerSL ℝ (a i)).toLinearMap) x = -b i} = facet a b i := by
    ext x
    simp only [facet, Set.mem_setOf_eq, LinearMap.neg_apply, ContinuousLinearMap.coe_coe,
      neg_inj]
    rfl
  rwa [hset] at h

/-- The direction space of the hyperplane carrying the facet. -/
theorem finrank_perp (v : EuclideanSpace ℝ (Fin d)) (hv : v ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = d - 1 := by
  have h1 : Module.finrank ℝ (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin d))) = 1 :=
    finrank_span_singleton hv
  have hadd := Submodule.finrank_add_finrank_orthogonal
    (K := (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin d))))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  omega

theorem mem_perp_iff (v z : EuclideanSpace ℝ (Fin d)) :
    z ∈ (ℝ ∙ v)ᗮ ↔ ⟪v, z⟫ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v)
  · intro h u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [real_inner_smul_left, h, mul_zero]

theorem facet_eq_image (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    (hrange : Set.range ψ = ((ℝ ∙ a i)ᗮ : Set (EuclideanSpace ℝ (Fin d))))
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ facet a b i) :
    chartMap ψ p '' (Hpoly (pullA ψ a) (pullB a b p)) = facet a b i := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(chartMap_mem_iff a b p y).mpr hy, ?_⟩
    have hmem : ψ y ∈ (ℝ ∙ a i)ᗮ := by
      rw [← SetLike.mem_coe, ← hrange]; exact ⟨y, rfl⟩
    have h0 : ⟪a i, ψ y⟫ = 0 := (mem_perp_iff _ _).mp hmem
    rw [chartMap, inner_add_right, h0, hp.2, add_zero]
  · intro hx
    have hxp : x - p ∈ (ℝ ∙ a i)ᗮ :=
      (mem_perp_iff _ _).mpr (by rw [inner_sub_right, hx.2, hp.2, sub_self])
    obtain ⟨y, hy⟩ : x - p ∈ Set.range ψ := by rw [hrange]; exact hxp
    have hxy : chartMap ψ p y = x := by rw [chartMap, hy]; abel
    refine ⟨y, ?_, hxy⟩
    rw [← chartMap_mem_iff a b p y, hxy]
    exact hx.1

theorem pullA_eq_zero (a : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hrange : Set.range ψ = ((ℝ ∙ a i)ᗮ : Set (EuclideanSpace ℝ (Fin d)))) :
    pullA ψ a i = 0 := by
  have hmem : ψ (pullA ψ a i) ∈ (ℝ ∙ a i)ᗮ := by
    rw [← SetLike.mem_coe, ← hrange]; exact ⟨_, rfl⟩
  have h0 : ⟪a i, ψ (pullA ψ a i)⟫ = 0 := (mem_perp_iff _ _).mp hmem
  have hself : ⟪pullA ψ a i, pullA ψ a i⟫ = 0 := by
    rw [pullA_inner a i (pullA ψ a i)]; exact h0
  rw [real_inner_self_eq_norm_sq] at hself
  have : ‖pullA ψ a i‖ = 0 := by nlinarith [norm_nonneg (pullA ψ a i)]
  exact norm_eq_zero.mp this

theorem pullB_eq_zero (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ∈ facet a b i) : pullB a b p i = 0 := by
  simp [pullB, hp.2]

/-- An always-satisfied inequality may be deleted. -/
theorem hpoly_drop {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin m)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (ha : a i = 0) (hb : 0 ≤ b i) :
    Hpoly a b = Hpoly (fun j => a (i.succAbove j)) (fun j => b (i.succAbove j)) := by
  ext y
  constructor
  · intro h j; exact h _
  · intro h j
    rcases eq_or_ne j i with rfl | hj
    · rw [ha]; simpa using hb
    · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
      exact h j'

set_option maxHeartbeats 1000000 in
/-- **The facet recursion.**  If every bounded polyhedron in `ℝ^(d-1)` cut out by `k`
inequalities has diameter at most `B`, then any two vertices of the facet of an
`(k+1)`-inequality polytope in `ℝ^d` are joined by a walk of `B` steps *in the polytope*. -/
theorem facet_reach {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (hai : a i ≠ 0) (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (facet a b i))
    (hv : v ∈ Set.extremePoints ℝ (facet a b i)) :
    Reach (Hpoly a b) B u v := by
  classical
  set p : EuclideanSpace ℝ (Fin d) := u with hpdef
  have hp : p ∈ facet a b i := hu.1
  obtain ⟨ψ, hrange⟩ := exists_chart ((ℝ ∙ a i)ᗮ) (d - 1) (finrank_perp (a i) hai)
  set A : Fin k → EuclideanSpace ℝ (Fin (d - 1)) :=
    fun j => pullA ψ a (i.succAbove j) with hA
  set Bv : Fin k → ℝ := fun j => pullB a b p (i.succAbove j) with hBv
  have hdrop : Hpoly (pullA ψ a) (pullB a b p) = Hpoly A Bv :=
    hpoly_drop _ _ i (pullA_eq_zero a i hrange) (le_of_eq (pullB_eq_zero a b i hp).symm)
  have himg : chartMap ψ p '' (Hpoly A Bv) = facet a b i := by
    rw [← hdrop]; exact facet_eq_image a b i hrange hp
  -- the chart of a bounded facet is bounded
  have hbdF : Bornology.IsBounded (facet a b i) := hbd.subset (facet_isExtreme a b i).1
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdF
  have hbdA : Bornology.IsBounded (Hpoly A Bv) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C + ‖p‖, fun y hy => ?_⟩
    have h1 : chartMap ψ p y ∈ facet a b i := by rw [← himg]; exact ⟨y, hy, rfl⟩
    have h3 : ψ y = chartMap ψ p y - p := by rw [chartMap]; abel
    calc ‖y‖ = ‖ψ y‖ := (ψ.norm_map y).symm
      _ = ‖chartMap ψ p y - p‖ := by rw [h3]
      _ ≤ ‖chartMap ψ p y‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ C + ‖p‖ := by linarith [hC _ h1]
  -- pull the two vertices back to the chart
  have hpull : ∀ z ∈ Set.extremePoints ℝ (facet a b i),
      ∃ y ∈ Set.extremePoints ℝ (Hpoly A Bv), chartMap ψ p y = z := by
    intro z hz
    have hzi : z ∈ chartMap ψ p '' (Hpoly A Bv) := by rw [himg]; exact hz.1
    obtain ⟨y, hy, hyz⟩ := hzi
    refine ⟨y, ?_, hyz⟩
    refine (chartMap_extremePoints (ψ := ψ) p (Hpoly A Bv) y).mpr ?_
    rw [hyz, himg]
    exact hz
  obtain ⟨yu, hyu, hyu2⟩ := hpull u hu
  obtain ⟨yv, hyv, hyv2⟩ := hpull v hv
  have hreach : Reach (Hpoly A Bv) B yu yv := IH A Bv hbdA yu hyu yv hyv
  have h2 := chartMap_reach (ψ := ψ) p hreach
  rw [himg, hyu2, hyv2] at h2
  exact reach_of_extreme (facet_isExtreme a b i) h2

end HirschFacet

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschFacet

namespace HirschLayer

variable {d n : ℕ}

/-! ## Vertices of a facet -/

theorem mem_extremePoints_facet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hui : ⟪a i, u⟫ = b i) : u ∈ Set.extremePoints ℝ (facet a b i) := by
  refine ⟨⟨hu.1, hui⟩, ?_⟩
  intro x1 h1 x2 h2 hseg
  exact hu.2 h1.1 h2.1 hseg

theorem extremePoints_facet_subset (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (i : Fin n) : Set.extremePoints ℝ (facet a b i) ⊆ Set.extremePoints ℝ (Hpoly a b) :=
  (facet_isExtreme a b i).extremePoints_subset_extremePoints

/-! ## The inequalities touched within `k` steps -/

open scoped Classical in
/-- The inequalities tight at some vertex reachable from `v` in at most `k` steps. -/
noncomputable def touched (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (k : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ w, w ∈ Set.extremePoints ℝ (Hpoly a b) ∧
    Reach (Hpoly a b) k v w ∧ ⟪a i, w⟫ = b i

theorem mem_touched (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (k : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    i ∈ touched a b k v ↔ ∃ w, w ∈ Set.extremePoints ℝ (Hpoly a b) ∧
      Reach (Hpoly a b) k v w ∧ ⟪a i, w⟫ = b i := by
  classical
  simp [touched]

theorem touched_mono (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) {k k' : ℕ}
    (hk : k ≤ k') (v : EuclideanSpace ℝ (Fin d)) : touched a b k v ⊆ touched a b k' v := by
  intro i hi
  obtain ⟨w, hw, hr, hb⟩ := (mem_touched a b k v i).mp hi
  exact (mem_touched a b k' v i).mpr ⟨w, hw, reach_mono _ hk hr, hb⟩

theorem card_touched_le (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (k : ℕ)
    (v : EuclideanSpace ℝ (Fin d)) : (touched a b k v).card ≤ n := by
  simpa using Finset.card_le_univ (touched a b k v)

/-- The vertex itself contributes all its own tight inequalities. -/
theorem tight_subset_touched (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (k : ℕ)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) (i : Fin n)
    (hi : ⟪a i, v⟫ = b i) : i ∈ touched a b k v :=
  (mem_touched a b k v i).mpr ⟨v, hv, reach_mono _ (Nat.zero_le k) (reach_zero _ v), hi⟩

/-! ## Walks run backwards -/

theorem adj_symm {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {x y : E}
    (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  rw [segment_symm]
  exact h.2

theorem reach_symm {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {L : ℕ} {x y : E}
    (h : Reach P L x y) : Reach P L y x := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  refine ⟨fun i => w (L - i), by simp [hL], by simp [h0], fun i hi => ?_⟩
  have hL1 : 1 ≤ L - i := by omega
  have hidx : L - i - 1 < L := by omega
  have hsucc : L - i - 1 + 1 = L - i := by omega
  have hstep' := hstep (L - i - 1) hidx
  rw [hsucc] at hstep'
  have hrw : L - (i + 1) = L - i - 1 := by omega
  dsimp only
  rw [hrw]
  rcases hstep' with he | hadj
  · exact Or.inl he.symm
  · exact Or.inr (adj_symm hadj)

/-! ## Pigeonhole -/

theorem exists_mem_inter_of_card {A B : Finset (Fin n)} (h : n < A.card + B.card) :
    (A ∩ B).Nonempty := by
  classical
  have hunion : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hle : (A ∪ B).card ≤ n := by simpa using Finset.card_le_univ (A ∪ B)
  have : 0 < (A ∩ B).card := by omega
  exact Finset.card_pos.mp this

/-- **Two half-covering layers meet.**  If the inequalities touched within `j` steps of `u`
and within `j'` steps of `v` each number more than half of all `n`, then some inequality is
touched by both — that is, some facet is reachable from both vertices. -/
theorem exists_common_touched (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {j j' : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (hu : n / 2 < (touched a b j u).card) (hv : n / 2 < (touched a b j' v).card) :
    ∃ i : Fin n, (∃ t, t ∈ Set.extremePoints ℝ (Hpoly a b) ∧
        Reach (Hpoly a b) j u t ∧ ⟪a i, t⟫ = b i) ∧
      (∃ s, s ∈ Set.extremePoints ℝ (Hpoly a b) ∧
        Reach (Hpoly a b) j' v s ∧ ⟪a i, s⟫ = b i) := by
  classical
  have hsum : n < (touched a b j u).card + (touched a b j' v).card := by omega
  obtain ⟨i, hi⟩ := exists_mem_inter_of_card hsum
  rw [Finset.mem_inter] at hi
  exact ⟨i, (mem_touched a b j u i).mp hi.1, (mem_touched a b j' v i).mp hi.2⟩


/-! ## The bridging step -/

set_option maxHeartbeats 1000000 in
/-- **The Kalai--Kleitman bridging step.**  Suppose every bounded H-polyhedron in
`ℝ^(d-1)` cut out by `k` inequalities has diameter at most `B`.  If the vertices within
`j` steps of `u` touch more than half of the inequalities, and likewise those within `j'`
steps of `v`, then some inequality is touched by both; crossing the facet it cuts out
joins `u` to `v` in `j + B + j'` steps. -/
theorem reach_via_common_facet {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    {j j' : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (htu : (k + 1) / 2 < (touched a b j u).card)
    (htv : (k + 1) / 2 < (touched a b j' v).card) :
    Reach (Hpoly a b) (j + B + j') u v := by
  obtain ⟨i, ⟨t, ht, hrt, hbt⟩, ⟨s, hs, hrs, hbs⟩⟩ := exists_common_touched a b htu htv
  have htf : t ∈ Set.extremePoints ℝ (facet a b i) := mem_extremePoints_facet a b i ht hbt
  have hsf : s ∈ Set.extremePoints ℝ (facet a b i) := mem_extremePoints_facet a b i hs hbs
  have hts : Reach (Hpoly a b) B t s := facet_reach a b i (hane i) hbd B IH htf hsf
  exact reach_trans _ (reach_trans _ hrt hts) (reach_symm _ hrs)

end HirschLayer

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple LinearOptimization

namespace HirschRelax

variable {d n : ℕ}

/-- Cutting an extreme subset down to a smaller ambient set keeps it extreme. -/
theorem isExtreme_inter {E : Type*} [AddCommGroup E] [Module ℝ E] {Q T S : Set E}
    (h : IsExtreme ℝ Q T) (hSQ : S ⊆ Q) : IsExtreme ℝ S (S ∩ T) := by
  constructor
  · exact Set.inter_subset_left
  · intro x1 h1 x2 h2 z hz hsg
    exact ⟨h1, h.2 (hSQ h1) (hSQ h2) hz.2 hsg⟩

/-- **Vertices survive the dropping of inequalities they do not touch.**  No simplicity
needed: an active basis of `d` independent tight rows is already contained in `F`. -/
theorem extreme_relax (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hF : tightSet a b u ⊆ F) :
    u ∈ Set.extremePoints ℝ (Hpoly (relaxA a F) (relaxB b F)) := by
  classical
  obtain ⟨s, hcard, htight, hind⟩ := exists_active_basis_indep a b hu
  have hsF : ∀ i ∈ s, i ∈ F := fun i hi =>
    hF (Finset.mem_filter.mpr ⟨Finset.mem_univ i, htight i hi⟩)
  refine extreme_of_indep_tight (relaxA a F) (relaxB b F) (subset_relax a b F hu.1)
    (s := s) ?_ ?_ hcard
  · intro i hi
    rw [relaxA_of_mem a F (hsF i hi), relaxB_of_mem b F (hsF i hi)]
    exact htight i hi
  · have h1 : (fun i : s => relaxA a F i.1) = (fun i : s => a i.1) := by
      funext i; exact relaxA_of_mem a F (hsF i.1 i.2)
    rw [h1]; exact hind

set_option maxHeartbeats 1000000 in
/-- **The dropped inequalities create no new neighbours.**  If every neighbour of the
vertex `x` in `P` touches only inequalities of `F`, then every neighbour of `x` in the
polyhedron cut out by `F` alone already lies in `P`.  Consequently distances in the
relaxed polyhedron are no smaller than in `P`. -/
theorem adj_relax_reflect (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b)) (hFx : tightSet a b x ⊆ F)
    (hadj : Adj (Hpoly (relaxA a F) (relaxB b F)) x y)
    (hnb : ∀ w, Adj (Hpoly a b) x w → tightSet a b w ⊆ F) :
    y ∈ Hpoly a b := by
  classical
  set A' := relaxA a F with hA'
  set B' := relaxB b F with hB'
  set φ : ℝ → EuclideanSpace ℝ (Fin d) := fun t => x + t • (y - x) with hφ
  have hlin : ∀ (j : Fin n) (s r : ℝ), ⟪a j, φ (s + r)⟫ = ⟪a j, φ s⟫ + r * ⟪a j, y - x⟫ := by
    intro j s r
    simp only [hφ, inner_add_right, real_inner_smul_right]
    ring
  have hsegeq : segment ℝ x y = φ '' Set.Icc 0 1 := segment_eq_image' ℝ x y
  have hsegP' : segment ℝ x y ⊆ Hpoly A' B' := hadj.2.1
  have hFhold : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ j ∈ F, ⟪a j, φ t⟫ ≤ b j := by
    intro t ht j hj
    have hmem : φ t ∈ Hpoly A' B' := hsegP' (by rw [hsegeq]; exact ⟨t, ht, rfl⟩)
    have hj2 := hmem j
    rwa [hA', hB', relaxA_of_mem a F hj, relaxB_of_mem b F hj] at hj2
  -- the parameters at which the segment is still inside `P`
  set S : Set ℝ := Set.Icc 0 1 ∩ φ ⁻¹' (Hpoly a b) with hSdef
  have hφcont : Continuous φ := by
    simp only [hφ]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hSclosed : IsClosed S := isClosed_Icc.inter ((hpoly_closed a b).preimage hφcont)
  have h0S : (0:ℝ) ∈ S := by
    refine ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩
    have : φ 0 = x := by simp [hφ]
    show φ 0 ∈ Hpoly a b
    rw [this]; exact hx.1
  have hScompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hSclosed Set.inter_subset_left
  set t : ℝ := sSup S with htdef
  have htS : t ∈ S := hScompact.sSup_mem ⟨0, h0S⟩
  have hle : ∀ s ∈ S, s ≤ t := fun s hs => le_csSup hScompact.bddAbove hs
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := htS.1
  have htP : φ t ∈ Hpoly a b := htS.2
  -- if the whole segment stays inside `P` we are done
  by_cases ht1 : t = 1
  · have hy1 : φ 1 = y := by simp [hφ]
    have : φ 1 ∈ Hpoly a b := by rw [← ht1]; exact htP
    rwa [hy1] at this
  exfalso
  have htlt : t < 1 := lt_of_le_of_ne ht01.2 ht1
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hadj.1)
  -- at the exit parameter some dropped inequality is tight
  have hexit : ∃ j, j ∉ F ∧ ⟪a j, φ t⟫ = b j := by
    by_contra hcon
    push_neg at hcon
    have hslack : ∀ j, j ∉ F → ⟪a j, φ t⟫ < b j := fun j hj =>
      lt_of_le_of_ne (htP j) (hcon j hj)
    set G : Finset (Fin n) := Finset.univ.filter (fun j => j ∉ F) with hG
    rcases Finset.eq_empty_or_nonempty G with hGe | hGne
    · -- every inequality survives, so the whole segment lies in `P`
      have h1S : (1:ℝ) ∈ S := by
        refine ⟨⟨zero_le_one, le_refl 1⟩, ?_⟩
        intro j
        refine hFhold 1 ⟨zero_le_one, le_refl 1⟩ j ?_
        by_contra hjF
        have : j ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjF⟩
        rw [hGe] at this
        simp at this
      exact absurd (hle 1 h1S) (not_le.mpr htlt)
    · set ε₀ : ℝ := G.inf' hGne (fun j => (b j - ⟪a j, φ t⟫) / (|⟪a j, y - x⟫| + 1)) with hε₀
      have hε₀pos : 0 < ε₀ := by
        rw [hε₀, Finset.lt_inf'_iff]
        intro j hj
        have hjF : j ∉ F := (Finset.mem_filter.mp hj).2
        exact div_pos (by linarith [hslack j hjF]) (by positivity)
      set ε : ℝ := min ε₀ (1 - t) with hεdef
      have hεpos : 0 < ε := lt_min hε₀pos (by linarith)
      have htεS : t + ε ∈ S := by
        refine ⟨⟨by linarith [ht01.1], by
          have : ε ≤ 1 - t := min_le_right _ _
          linarith⟩, ?_⟩
        intro j
        by_cases hjF : j ∈ F
        · exact hFhold (t + ε) ⟨by linarith [ht01.1], by
            have : ε ≤ 1 - t := min_le_right _ _
            linarith⟩ j hjF
        · have hjG : j ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjF⟩
          have hbnd : ε₀ ≤ (b j - ⟪a j, φ t⟫) / (|⟪a j, y - x⟫| + 1) := by
            rw [hε₀]; exact Finset.inf'_le _ hjG
          have hd1 : (0:ℝ) < |⟪a j, y - x⟫| + 1 := by positivity
          have hmul : ε * (|⟪a j, y - x⟫| + 1) ≤ b j - ⟪a j, φ t⟫ := by
            have hle0 : ε ≤ (b j - ⟪a j, φ t⟫) / (|⟪a j, y - x⟫| + 1) :=
              le_trans (min_le_left _ _) hbnd
            rw [le_div_iff₀ hd1] at hle0
            exact hle0
          have habs : ⟪a j, y - x⟫ ≤ |⟪a j, y - x⟫| := le_abs_self _
          have : ε * ⟪a j, y - x⟫ ≤ ε * (|⟪a j, y - x⟫| + 1) := by nlinarith
          rw [hlin j t ε]
          linarith
      have : t + ε ≤ t := hle _ htεS
      linarith
  obtain ⟨j, hjF, hjz⟩ := hexit
  -- the exit point is a vertex of `P` adjacent to `x`
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht01.1 with h | h
    · exact h
    · exfalso
      have hzx : φ t = x := by rw [← h]; simp [hφ]
      have hjx : j ∈ tightSet a b x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, by rw [← hzx]; exact hjz⟩
      exact hjF (hFx hjx)
  have hzne : φ t ≠ x := by
    intro hc
    have h1 : t • (y - x) = 0 := by
      have : x + t • (y - x) = x := hc
      simpa using this
    rcases smul_eq_zero.mp h1 with h | h
    · exact absurd h (ne_of_gt htpos)
    · exact hyx h
  have hzmem : φ t ∈ segment ℝ x y := by rw [hsegeq]; exact ⟨t, ht01, rfl⟩
  have hKext : IsExtreme ℝ (Hpoly a b) (Hpoly a b ∩ segment ℝ x y) :=
    isExtreme_inter hadj.2 (subset_relax a b F)
  have hKeq : Hpoly a b ∩ segment ℝ x y = segment ℝ x (φ t) := by
    apply Set.Subset.antisymm
    · rintro w ⟨hwP, hwseg⟩
      rw [hsegeq] at hwseg
      obtain ⟨r, hr, hrw⟩ := hwseg
      have hrS : r ∈ S := ⟨hr, by show φ r ∈ Hpoly a b; rw [hrw]; exact hwP⟩
      have hrt : r ≤ t := hle r hrS
      rw [segment_eq_image' ℝ x (φ t)]
      refine ⟨r / t, ⟨div_nonneg hr.1 htpos.le, by rw [div_le_one htpos]; exact hrt⟩, ?_⟩
      have hzx : φ t - x = t • (y - x) := by simp [hφ]
      dsimp only
      rw [hzx, smul_smul, div_mul_cancel₀ _ (ne_of_gt htpos), ← hrw]
    · intro w hw
      exact ⟨(hpoly_convex a b).segment_subset hx.1 htP hw,
        (convex_segment x y).segment_subset (left_mem_segment ℝ x y) hzmem hw⟩
  rw [hKeq] at hKext
  have hadjxz : Adj (Hpoly a b) x (φ t) := ⟨Ne.symm hzne, hKext⟩
  have hjt : j ∈ tightSet a b (φ t) := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjz⟩
  exact hjF (hnb (φ t) hadjxz hjt)

/-- An edge of the relaxed polyhedron whose endpoints both lie in `P` is an edge of `P`. -/
theorem adj_of_relax_adj (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) {x y : EuclideanSpace ℝ (Fin d)} (hxP : x ∈ Hpoly a b)
    (hyP : y ∈ Hpoly a b) (hadj : Adj (Hpoly (relaxA a F) (relaxB b F)) x y) :
    Adj (Hpoly a b) x y := by
  refine ⟨hadj.1, ?_⟩
  have h := isExtreme_inter hadj.2 (subset_relax a b F)
  have heq : Hpoly a b ∩ segment ℝ x y = segment ℝ x y :=
    Set.inter_eq_right.mpr ((hpoly_convex a b).segment_subset hxP hyP)
  rwa [heq] at h

set_option maxHeartbeats 1000000 in
/-- **No shortcuts.**  If every vertex of `P` within `k` steps of `v` touches only
inequalities of `F`, then a walk of `k` steps from `v` in the relaxed polyhedron is
already a walk in `P`.  Distances from `v` up to `k` are therefore the same in both. -/
theorem reach_of_relax_reach (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (k : ℕ) {v z : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hlayer : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ k ∧ Reach (Hpoly a b) L v w) → tightSet a b w ⊆ F)
    (h : Reach (Hpoly (relaxA a F) (relaxB b F)) k v z) :
    Reach (Hpoly a b) k v z := by
  obtain ⟨w, h0, hk, hstep⟩ := h
  have key : ∀ i, i ≤ k →
      Reach (Hpoly a b) i v (w i) ∧ w i ∈ Set.extremePoints ℝ (Hpoly a b) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨by rw [h0]; exact reach_zero _ v, by rw [h0]; exact hv⟩
    | succ i ih =>
        intro hik
        obtain ⟨hri, hvi⟩ := ih (by omega)
        have hFi : tightSet a b (w i) ⊆ F := hlayer _ hvi ⟨i, by omega, hri⟩
        rcases hstep i (by omega) with he | hadj
        · exact ⟨by rw [← he]; exact reach_succ _ _ _ _ hri, by rw [← he]; exact hvi⟩
        · have hyP : w (i + 1) ∈ Hpoly a b := by
            refine adj_relax_reflect a b F hvi hFi hadj ?_
            intro u hu
            refine hlayer u (adj_right_mem_extremePoints hu) ⟨i + 1, hik, ?_⟩
            exact reach_trans _ hri (reach_one_of_adj _ hu)
          have hadjP : Adj (Hpoly a b) (w i) (w (i + 1)) :=
            adj_of_relax_adj a b F hvi.1 hyP hadj
          exact ⟨reach_trans _ hri (reach_one_of_adj _ hadjP),
            adj_right_mem_extremePoints hadjP⟩
  have hfin := (key k (le_refl k)).1
  rwa [hk] at hfin

/-- **Kalai--Kleitman's radius bound.**  If all vertices within `k` steps of `v` touch only
the inequalities of `F`, and the polyhedron cut out by `F` alone has diameter at most `Δ`,
then `k ≤ Δ` — provided some vertex really is at distance `k` from `v`. -/
theorem layer_radius_le (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (Δ k : ℕ) {v t : EuclideanSpace ℝ (Fin d)}
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (ht : t ∈ Set.extremePoints ℝ (Hpoly a b))
    (hlayer : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ k ∧ Reach (Hpoly a b) L v w) → tightSet a b w ⊆ F)
    (hFv : tightSet a b v ⊆ F)
    (htreach : ∃ L, L ≤ k ∧ Reach (Hpoly a b) L v t)
    (hfar : ∀ L, Reach (Hpoly a b) L v t → k ≤ L)
    (hdiam : DiamLE (Hpoly (relaxA a F) (relaxB b F)) Δ) : k ≤ Δ := by
  by_contra hcon
  push_neg at hcon
  have hFt : tightSet a b t ⊆ F := hlayer t ht htreach
  have hvP' := extreme_relax a b F hv hFv
  have htP' := extreme_relax a b F ht hFt
  have hr : Reach (Hpoly (relaxA a F) (relaxB b F)) Δ v t := hdiam v hvP' t htP'
  have hlayer' : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ Δ ∧ Reach (Hpoly a b) L v w) → tightSet a b w ⊆ F := by
    rintro w hw ⟨L, hL, hRL⟩
    exact hlayer w hw ⟨L, by omega, hRL⟩
  have := reach_of_relax_reach a b F Δ hv hlayer' hr
  exact absurd (hfar Δ this) (by omega)

end HirschRelax

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschSimple

namespace HirschReindex

variable {d n : ℕ}

/-- The relaxed polyhedron, re-indexed by `Fin F.card`. -/
theorem hpoly_relax_reindex (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) :
    Hpoly (relaxA a F) (relaxB b F)
      = Hpoly (fun j : Fin F.card => a ((F.equivFin.symm j : F) : Fin n))
              (fun j : Fin F.card => b ((F.equivFin.symm j : F) : Fin n)) := by
  ext x
  constructor
  · intro hx j
    have hmem : ((F.equivFin.symm j : F) : Fin n) ∈ F := (F.equivFin.symm j).2
    have := hx ((F.equivFin.symm j : F) : Fin n)
    rwa [relaxA_of_mem a F hmem, relaxB_of_mem b F hmem] at this
  · intro hx i
    by_cases hi : i ∈ F
    · have := hx (F.equivFin ⟨i, hi⟩)
      simp only [Equiv.symm_apply_apply] at this
      rwa [relaxA_of_mem a F hi, relaxB_of_mem b F hi]
    · simp only [relaxA, relaxB, if_neg hi, inner_zero_left]
      norm_num

/-- Rows that the relaxed polyhedron already satisfies may be dropped. -/
theorem hpoly_eq_relax (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n))
    (h : ∀ i, i ∉ F → ∀ x ∈ Hpoly (relaxA a F) (relaxB b F), ⟪a i, x⟫ ≤ b i) :
    Hpoly a b = Hpoly (relaxA a F) (relaxB b F) := by
  refine Set.Subset.antisymm (subset_relax a b F) ?_
  intro x hx i
  by_cases hi : i ∈ F
  · have := hx i
    rwa [relaxA_of_mem a F hi, relaxB_of_mem b F hi] at this
  · exact h i hi x hx

/-- A row with vanishing normal and negative right-hand side makes the polyhedron empty. -/
theorem hpoly_eq_empty (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) (i : Fin n)
    (hai : a i = 0) (hbi : b i < 0) : Hpoly a b = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have := hx i
  rw [hai, inner_zero_left] at this
  linarith

/-- The zero rows of a nonempty H-polyhedron are vacuous, so it is cut out by its rows
with nonzero normal alone. -/
theorem hpoly_eq_relax_nonzero (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) :
    Hpoly a b = Hpoly (relaxA a (Finset.univ.filter fun i => a i ≠ 0))
      (relaxB b (Finset.univ.filter fun i => a i ≠ 0)) := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  refine hpoly_eq_relax a b _ ?_
  intro i hi x _
  have hai : a i = 0 := by
    by_contra hc
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
  have hb0 : (0:ℝ) ≤ b i := by
    have := hx0 i
    rwa [hai, inner_zero_left] at this
  rw [hai, inner_zero_left]
  exact hb0

/-- The number of rows with nonzero normal never exceeds `n`. -/
theorem card_nonzero_le (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    (Finset.univ.filter fun i => a i ≠ 0).card ≤ n := by
  classical
  simpa using Finset.card_le_univ (Finset.univ.filter fun i => a i ≠ 0)

/-- Every remaining row really has a nonzero normal. -/
theorem reindex_ne_zero (a : Fin n → EuclideanSpace ℝ (Fin d)) (F : Finset (Fin n))
    (hF : ∀ i ∈ F, a i ≠ 0) (j : Fin F.card) :
    a ((F.equivFin.symm j : F) : Fin n) ≠ 0 :=
  hF _ (F.equivFin.symm j).2

/-- `DiamLE` is preserved by rewriting the polyhedron along an equality. -/
theorem diamLE_congr {E : Type*} [AddCommGroup E] [Module ℝ E] {P Q : Set E} (h : P = Q)
    {B : ℕ} (hd : DiamLE P B) : DiamLE Q B := by rw [← h]; exact hd

/-- An empty polyhedron has diameter zero. -/
theorem diamLE_empty {E : Type*} [AddCommGroup E] [Module ℝ E] (B : ℕ) :
    DiamLE (∅ : Set E) B := by
  intro u hu
  exact absurd hu.1 (by simp)

end HirschReindex

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschFacet
open HirschLayer HirschRelax

namespace HirschKK

variable {d n : ℕ}

/-- Walks stay among vertices. -/
theorem reach_mem_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E}
    {L : ℕ} {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (h : Reach P L u v) :
    v ∈ Set.extremePoints ℝ P := by
  obtain ⟨w, h0, hL, hstep⟩ := h
  have key : ∀ i, i ≤ L → w i ∈ Set.extremePoints ℝ P := by
    intro i
    induction i with
    | zero => intro _; rw [h0]; exact hu
    | succ i ih =>
        intro hi
        rcases hstep i (by omega) with he | hadj
        · rw [← he]; exact ih (by omega)
        · exact adj_right_mem_extremePoints hadj
  rw [← hL]; exact key L (le_refl L)

/-- A walk of length `L` contains walks of every shorter length to its intermediate
points. -/
theorem reach_prefix {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {L : ℕ} {u : E}
    {w : ℕ → E} (h0 : w 0 = u)
    (hstep : ∀ i < L, w i = w (i + 1) ∨ Adj P (w i) (w (i + 1))) {r : ℕ} (hr : r ≤ L) :
    Reach P r u (w r) :=
  ⟨w, h0, rfl, fun i hi => hstep i (lt_of_lt_of_le hi hr)⟩

set_option maxHeartbeats 1000000 in
/-- **The radius of a layer is at most the diameter of its relaxation.**  Here `F` holds
every inequality touched within `r` steps of `u`, and some inequality is touched at step
`r+1` for the first time. -/
theorem layer_radius_le_diam (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (Δ r : ℕ) {u : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hlayer : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ r ∧ Reach (Hpoly a b) L u w) → tightSet a b w ⊆ F)
    (hgrow : ∃ i, i ∈ touched a b (r + 1) u ∧ i ∉ touched a b r u)
    (hdiam : DiamLE (Hpoly (relaxA a F) (relaxB b F)) Δ) : r ≤ Δ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hΔr : Δ < r := hcon
  have hFu : tightSet a b u ⊆ F :=
    hlayer u hu ⟨0, Nat.zero_le r, reach_zero _ u⟩
  have huP' : u ∈ Set.extremePoints ℝ (Hpoly (relaxA a F) (relaxB b F)) :=
    extreme_relax a b F hu hFu
  -- inside the layer, every vertex is already within `Δ` steps
  have hshort : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ r ∧ Reach (Hpoly a b) L u w) → Reach (Hpoly a b) Δ u w := by
    intro w hw hLw
    have hFw : tightSet a b w ⊆ F := hlayer w hw hLw
    have hwP' : w ∈ Set.extremePoints ℝ (Hpoly (relaxA a F) (relaxB b F)) :=
      extreme_relax a b F hw hFw
    have hr' : Reach (Hpoly (relaxA a F) (relaxB b F)) Δ u w := hdiam u huP' w hwP'
    refine reach_of_relax_reach a b F Δ hu ?_ hr'
    rintro z hz ⟨L, hL, hRL⟩
    exact hlayer z hz ⟨L, by omega, hRL⟩
  -- the newly touched inequality is already touched at step `r`
  obtain ⟨i, hi1, hi2⟩ := hgrow
  obtain ⟨t, htv, htr, htb⟩ := (mem_touched a b (r + 1) u i).mp hi1
  obtain ⟨w, h0, hL, hstep⟩ := htr
  have hwr : Reach (Hpoly a b) r u (w r) := reach_prefix h0 hstep (Nat.le_succ r)
  have hwrv : w r ∈ Set.extremePoints ℝ (Hpoly a b) := reach_mem_extremePoints hu hwr
  have hwrΔ : Reach (Hpoly a b) Δ u (w r) := hshort _ hwrv ⟨r, le_refl r, hwr⟩
  have htΔ : Reach (Hpoly a b) r u t := by
    rcases hstep r (Nat.lt_succ_self r) with he | hadj
    · have : Reach (Hpoly a b) Δ u (w (r + 1)) := by rw [← he]; exact hwrΔ
      rw [hL] at this
      exact reach_mono _ (le_of_lt hΔr) this
    · have h1 : Reach (Hpoly a b) (Δ + 1) u (w (r + 1)) :=
        reach_trans _ hwrΔ (reach_one_of_adj _ hadj)
      rw [hL] at h1
      exact reach_mono _ (by omega) h1
  exact hi2 ((mem_touched a b r u i).mpr ⟨t, htv, htΔ, htb⟩)

set_option maxHeartbeats 1000000 in
/-- **Half of the inequalities are touched quickly.**  Suppose the layers around `u`
eventually touch more than `h` of the inequalities, and every polyhedron cut out by at
most `h` of them has diameter at most `Δ`.  Then more than `h` inequalities are already
touched within `Δ + 1` steps of `u`. -/
theorem exists_short_half_cover (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (h Δ : ℕ) {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hbig : ∃ k, h < (touched a b k u).card)
    (hdiam : ∀ F : Finset (Fin n), F.card ≤ h →
      DiamLE (Hpoly (relaxA a F) (relaxB b F)) Δ) :
    ∃ j, j ≤ Δ + 1 ∧ h < (touched a b j u).card := by
  classical
  have hspec : h < (touched a b (Nat.find hbig) u).card := Nat.find_spec hbig
  rcases Nat.eq_zero_or_pos (Nat.find hbig) with h0 | hpos
  · exact ⟨0, Nat.zero_le _, by rw [← h0]; exact hspec⟩
  obtain ⟨r, hr⟩ : ∃ r, Nat.find hbig = r + 1 := ⟨Nat.find hbig - 1, by omega⟩
  have hbig' : h < (touched a b (r + 1) u).card := by rw [← hr]; exact hspec
  have hrle : (touched a b r u).card ≤ h := by
    by_contra hc
    push_neg at hc
    have hfl : Nat.find hbig ≤ r := Nat.find_le hc
    omega
  have hgrow : ∃ i, i ∈ touched a b (r + 1) u ∧ i ∉ touched a b r u := by
    by_contra hc
    push_neg at hc
    have hsub : touched a b (r + 1) u ⊆ touched a b r u := fun i hi => hc i hi
    have hcard := Finset.card_le_card hsub
    omega
  have hlayer : ∀ w ∈ Set.extremePoints ℝ (Hpoly a b),
      (∃ L, L ≤ r ∧ Reach (Hpoly a b) L u w) → tightSet a b w ⊆ touched a b r u := by
    rintro w hw ⟨L, hL, hRL⟩ i hi
    exact (mem_touched a b r u i).mpr
      ⟨w, hw, reach_mono _ hL hRL, (Finset.mem_filter.mp hi).2⟩
  have hrΔ : r ≤ Δ :=
    layer_radius_le_diam a b (touched a b r u) Δ r hu hlayer hgrow (hdiam _ hrle)
  exact ⟨r + 1, by omega, hbig'⟩

set_option maxHeartbeats 1000000 in
/-- **The Kalai--Kleitman recursion.**  Let `P` be a bounded polytope in `ℝ^d` cut out by
`n = k+1` inequalities, all with nonzero normal, and whose vertex-edge graph is connected.
If every bounded polyhedron in `ℝ^(d-1)` with `k` inequalities has diameter at most `B₁`,
and every polyhedron cut out by at most `⌊n/2⌋` of our own inequalities has diameter at
most `B₂`, then `P` has diameter at most `2 B₂ + B₁ + 2`.

This is `Δ(d,n) ≤ Δ(d-1,n-1) + 2 Δ(d,⌊n/2⌋) + 2`. -/
theorem kk_recursion {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B₁ B₂ : ℕ)
    (IH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B₁)
    (IH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
      DiamLE (Hpoly (relaxA a F) (relaxB b F)) B₂)
    (hconn : ∀ u ∈ Set.extremePoints ℝ (Hpoly a b), ∀ v ∈ Set.extremePoints ℝ (Hpoly a b),
      ∃ L, Reach (Hpoly a b) L u v) :
    DiamLE (Hpoly a b) (2 * B₂ + B₁ + 2) := by
  classical
  refine diamLE_of_reach _ _ ?_
  intro u hu v hv
  -- the case where the layers around a vertex never cover half of the inequalities
  have hsmall : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ y ∈ Set.extremePoints ℝ (Hpoly a b),
      (¬ ∃ j, (k + 1) / 2 < (touched a b j x).card) → Reach (Hpoly a b) B₂ x y := by
    intro x hx y hy hnb
    push_neg at hnb
    obtain ⟨L, hL⟩ := hconn x hx y hy
    set M := max L B₂ with hM
    set F := touched a b M x with hF
    have hFcard : F.card ≤ (k + 1) / 2 := hnb M
    have hFx : tightSet a b x ⊆ F := by
      intro i hi
      exact tight_subset_touched a b M hx i (Finset.mem_filter.mp hi).2
    have hFy : tightSet a b y ⊆ F := by
      intro i hi
      exact (mem_touched a b M x i).mpr
        ⟨y, hy, reach_mono _ (le_max_left L B₂) hL, (Finset.mem_filter.mp hi).2⟩
    have hxP' := extreme_relax a b F hx hFx
    have hyP' := extreme_relax a b F hy hFy
    have hr : Reach (Hpoly (relaxA a F) (relaxB b F)) B₂ x y := IH2 F hFcard x hxP' y hyP'
    refine reach_of_relax_reach a b F B₂ hx ?_ hr
    rintro w hw ⟨L', hL', hRL'⟩ i hi
    exact (mem_touched a b M x i).mpr
      ⟨w, hw, reach_mono _ (le_trans hL' (le_max_right L B₂)) hRL',
        (Finset.mem_filter.mp hi).2⟩
  by_cases hbu : ∃ j, (k + 1) / 2 < (touched a b j u).card
  · by_cases hbv : ∃ j, (k + 1) / 2 < (touched a b j v).card
    · obtain ⟨j, hj, hju⟩ := exists_short_half_cover a b ((k + 1) / 2) B₂ hu hbu IH2
      obtain ⟨j', hj', hjv⟩ := exists_short_half_cover a b ((k + 1) / 2) B₂ hv hbv IH2
      exact ⟨j + B₁ + j', by omega,
        reach_via_common_facet a b hane hbd B₁ IH1 hju hjv⟩
    · exact ⟨B₂, by omega, reach_symm _ (hsmall v hv u hu hbv)⟩
  · exact ⟨B₂, by omega, hsmall u hu v hv hbu⟩

end HirschKK

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschFacet
open HirschLayer HirschRelax HirschKK LinearOptimization

namespace HirschKK2

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
/-- The facet recursion, without a boundedness hypothesis. -/
theorem facet_reach' {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (facet a b i))
    (hv : v ∈ Set.extremePoints ℝ (facet a b i)) :
    Reach (Hpoly a b) B u v := by
  classical
  set p : EuclideanSpace ℝ (Fin d) := u with hpdef
  have hp : p ∈ facet a b i := hu.1
  obtain ⟨ψ, hrange⟩ := exists_chart ((ℝ ∙ a i)ᗮ) (d - 1) (finrank_perp (a i) hai)
  set A : Fin k → EuclideanSpace ℝ (Fin (d - 1)) :=
    fun j => pullA ψ a (i.succAbove j) with hA
  set Bv : Fin k → ℝ := fun j => pullB a b p (i.succAbove j) with hBv
  have hdrop : Hpoly (pullA ψ a) (pullB a b p) = Hpoly A Bv :=
    hpoly_drop _ _ i (pullA_eq_zero a i hrange) (le_of_eq (pullB_eq_zero a b i hp).symm)
  have himg : chartMap ψ p '' (Hpoly A Bv) = facet a b i := by
    rw [← hdrop]; exact facet_eq_image a b i hrange hp
  have hpull : ∀ z ∈ Set.extremePoints ℝ (facet a b i),
      ∃ y ∈ Set.extremePoints ℝ (Hpoly A Bv), chartMap ψ p y = z := by
    intro z hz
    have hzi : z ∈ chartMap ψ p '' (Hpoly A Bv) := by rw [himg]; exact hz.1
    obtain ⟨y, hy, hyz⟩ := hzi
    refine ⟨y, ?_, hyz⟩
    refine (chartMap_extremePoints (ψ := ψ) p (Hpoly A Bv) y).mpr ?_
    rw [hyz, himg]
    exact hz
  obtain ⟨yu, hyu, hyu2⟩ := hpull u hu
  obtain ⟨yv, hyv, hyv2⟩ := hpull v hv
  have hreach : Reach (Hpoly A Bv) B yu yv := IH A Bv yu hyu yv hyv
  have h2 := chartMap_reach (ψ := ψ) p hreach
  rw [himg, hyu2, hyv2] at h2
  exact reach_of_extreme (facet_isExtreme a b i) h2

/-- The bridging step, without a boundedness hypothesis. -/
theorem reach_via_common_facet' {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B)
    {j j' : ℕ} {u v : EuclideanSpace ℝ (Fin d)}
    (htu : (k + 1) / 2 < (touched a b j u).card)
    (htv : (k + 1) / 2 < (touched a b j' v).card) :
    Reach (Hpoly a b) (j + B + j') u v := by
  obtain ⟨i, ⟨t, ht, hrt, hbt⟩, ⟨s, hs, hrs, hbs⟩⟩ := exists_common_touched a b htu htv
  have htf : t ∈ Set.extremePoints ℝ (facet a b i) := mem_extremePoints_facet a b i ht hbt
  have hsf : s ∈ Set.extremePoints ℝ (facet a b i) := mem_extremePoints_facet a b i hs hbs
  have hts : Reach (Hpoly a b) B t s := facet_reach' a b i (hane i) B IH htf hsf
  exact reach_trans _ (reach_trans _ hrt hts) (reach_symm _ hrs)

set_option maxHeartbeats 1000000 in
/-- **The Kalai--Kleitman recursion for arbitrary H-polyhedra.**
`Δ(d,n) ≤ Δ(d-1,n-1) + 2 Δ(d,⌊n/2⌋) + 2`, with no boundedness or connectivity
hypothesis. -/
theorem kk_recursion' {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0) (B₁ B₂ : ℕ)
    (IH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B₁)
    (IH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
      DiamLE (Hpoly (relaxA a F) (relaxB b F)) B₂) :
    DiamLE (Hpoly a b) (2 * B₂ + B₁ + 2) := by
  classical
  refine diamLE_of_reach _ _ ?_
  intro u hu v hv
  have hsmall : ∀ x ∈ Set.extremePoints ℝ (Hpoly a b), ∀ y ∈ Set.extremePoints ℝ (Hpoly a b),
      (¬ ∃ j, (k + 1) / 2 < (touched a b j x).card) → Reach (Hpoly a b) B₂ x y := by
    intro x hx y hy hnb
    push_neg at hnb
    obtain ⟨L, hL⟩ := Hirsch.graph_connected_general d (k + 1) a b x y hx hy
    set M := max L B₂ with hM
    set F := touched a b M x with hF
    have hFcard : F.card ≤ (k + 1) / 2 := hnb M
    have hFx : tightSet a b x ⊆ F := by
      intro i hi
      exact tight_subset_touched a b M hx i (Finset.mem_filter.mp hi).2
    have hFy : tightSet a b y ⊆ F := by
      intro i hi
      exact (mem_touched a b M x i).mpr
        ⟨y, hy, reach_mono _ (le_max_left L B₂) hL, (Finset.mem_filter.mp hi).2⟩
    have hxP' := extreme_relax a b F hx hFx
    have hyP' := extreme_relax a b F hy hFy
    have hr : Reach (Hpoly (relaxA a F) (relaxB b F)) B₂ x y := IH2 F hFcard x hxP' y hyP'
    refine reach_of_relax_reach a b F B₂ hx ?_ hr
    rintro w hw ⟨L', hL', hRL'⟩ i hi
    exact (mem_touched a b M x i).mpr
      ⟨w, hw, reach_mono _ (le_trans hL' (le_max_right L B₂)) hRL',
        (Finset.mem_filter.mp hi).2⟩
  by_cases hbu : ∃ j, (k + 1) / 2 < (touched a b j u).card
  · by_cases hbv : ∃ j, (k + 1) / 2 < (touched a b j v).card
    · obtain ⟨j, hj, hju⟩ := exists_short_half_cover a b ((k + 1) / 2) B₂ hu hbu IH2
      obtain ⟨j', hj', hjv⟩ := exists_short_half_cover a b ((k + 1) / 2) B₂ hv hbv IH2
      exact ⟨j + B₁ + j', by omega, reach_via_common_facet' a b hane B₁ IH1 hju hjv⟩
    · exact ⟨B₂, by omega, reach_symm _ (hsmall v hv u hu hbv)⟩
  · exact ⟨B₂, by omega, hsmall u hu v hv hbu⟩

end HirschKK2

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschFacet
open HirschLayer HirschRelax HirschReindex HirschKK HirschKK2 LinearOptimization

namespace HirschKKb

/-! ## Base cases -/

set_option maxHeartbeats 1000000 in
/-- With at most `d` inequalities a polyhedron in `ℝ^d` has at most one vertex. -/
theorem diamLE_of_n_le_d {d n : ℕ} (hnd : n ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) : DiamLE (Hpoly a b) 0 := by
  classical
  refine diamLE_of_subsingleton _ _ (fun u hu v hv => ?_)
  obtain ⟨s, hscard, hstight, hsind⟩ := exists_active_basis_indep a b hu
  obtain ⟨t, htcard, httight, htind⟩ := exists_active_basis_indep a b hv
  have hsu : s = Finset.univ := by
    refine Finset.eq_univ_of_card s ?_
    have := Finset.card_le_univ s
    simp only [Finset.card_univ, Fintype.card_fin] at this ⊢
    omega
  have htu : t = Finset.univ := by
    refine Finset.eq_univ_of_card t ?_
    have := Finset.card_le_univ t
    simp only [Finset.card_univ, Fintype.card_fin] at this ⊢
    omega
  have hall : ∀ i : Fin n, ⟪a i, u⟫ = b i := fun i => hstight i (hsu ▸ Finset.mem_univ i)
  have hallv : ∀ i : Fin n, ⟪a i, v⟫ = b i := fun i => httight i (htu ▸ Finset.mem_univ i)
  have hspan : Submodule.span ℝ (Set.range (fun i : s => a i.1)) = ⊤ := by
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : s => a i.1))) = d := by
      rw [finrank_span_eq_card hsind]; simp [hscard]
    exact Submodule.eq_top_of_finrank_eq (by rw [hfr]; simp)
  have hdiff : ∀ i ∈ s, ⟪a i, u - v⟫ = 0 := by
    intro i _
    rw [inner_sub_right, hall i, hallv i, sub_self]
  have hzero : ∀ w : EuclideanSpace ℝ (Fin d), ⟪w, u - v⟫ = 0 := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Set.range (fun i : s => a i.1)) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hdiff i.1 i.2
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy]; ring
    | smul c x _ hx => rw [real_inner_smul_left, hx]; ring
  have h0 := hzero (u - v)
  rw [real_inner_self_eq_norm_sq] at h0
  have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- In dimension at most one the polyhedron is a point, a segment, a ray or a line, so
any two vertices are equal or adjacent. -/
theorem diamLE_dim_le_one {d n : ℕ} (hd : d ≤ 1) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) : DiamLE (Hpoly a b) 1 := by
  refine diamLE_of_adj _ _ le_rfl (fun u hu v hv => ?_)
  by_cases huv : u = v
  · exact Or.inl huv
  refine Or.inr ⟨huv, ?_⟩
  have hrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) ≤ 1 := by simp [hd]
  have hseg := eq_segment_of_finrank_le_one hrk _ (hpoly_convex a b) hu hv huv
  rw [← hseg]
  exact IsExtreme.refl _ _

theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) {B B' : ℕ}
    (hB : B ≤ B') (h : DiamLE P B) : DiamLE P B' :=
  diamLE_of_reach P B' (fun u hu v hv => ⟨B, hB, h u hu v hv⟩)

end HirschKKb

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschFacet
open HirschLayer HirschKK2 LinearOptimization

namespace HirschShare

variable {d n : ℕ}

/-- A vertex touches at least `d` inequalities. -/
theorem d_le_card_tightSet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) :
    d ≤ (tightSet a b u).card := by
  classical
  obtain ⟨s, hscard, hstight, -⟩ := exists_active_basis_indep a b hu
  have hsub : s ⊆ tightSet a b u := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hstight i hi⟩
  calc d = s.card := hscard.symm
    _ ≤ (tightSet a b u).card := Finset.card_le_card hsub

/-- With fewer than `2d` inequalities, any two vertices touch a common one. -/
theorem exists_common_tight (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hn : n < 2 * d) {u v : EuclideanSpace ℝ (Fin d)}
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b)) (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    ∃ i : Fin n, ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  classical
  have hcu := d_le_card_tightSet a b hu
  have hcv := d_le_card_tightSet a b hv
  have hunion : (tightSet a b u ∪ tightSet a b v).card ≤ n := by
    simpa using Finset.card_le_univ (tightSet a b u ∪ tightSet a b v)
  have hcard := Finset.card_union_add_card_inter (tightSet a b u) (tightSet a b v)
  have hpos : 0 < (tightSet a b u ∩ tightSet a b v).card := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter] at hi
  exact ⟨i, (Finset.mem_filter.mp hi.1).2, (Finset.mem_filter.mp hi.2).2⟩

/-- **`Δ(d,n) ≤ Δ(d-1,n-1)` when `n < 2d`.** -/
theorem reach_of_few_rows {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0) (hn : k + 1 < 2 * d) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B)
    {u v : EuclideanSpace ℝ (Fin d)} (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) : Reach (Hpoly a b) B u v := by
  obtain ⟨i, hiu, hiv⟩ := exists_common_tight a b hn hu hv
  exact facet_reach' a b i (hane i) B IH
    (mem_extremePoints_facet a b i hu hiu) (mem_extremePoints_facet a b i hv hiv)

/-- The same, as a diameter bound. -/
theorem diamLE_of_few_rows {k : ℕ} (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (hane : ∀ i, a i ≠ 0) (hn : k + 1 < 2 * d) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') B) : DiamLE (Hpoly a b) B :=
  diamLE_of_reach _ _ (fun u hu v hv => ⟨B, le_rfl, reach_of_few_rows a b hane hn B IH hu hv⟩)

end HirschShare

namespace HirschToddArith

/-- The polynomial core: `√m (m + 6) ≥ 3m + 6` for `m ≥ 5`. -/
theorem sqrt_core {m : ℝ} (hm : 5 ≤ m) : 3 * m + 6 ≤ Real.sqrt m * (m + 6) := by
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0
  have hsnn : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  have hkey : (3 * m + 6) ^ 2 ≤ (Real.sqrt m * (m + 6)) ^ 2 := by
    have hexp : (Real.sqrt m * (m + 6)) ^ 2 = m * (m + 6) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hm0]
    rw [hexp]
    nlinarith [sq_nonneg (m - 5), sq_nonneg m, hm]
  have hpos : 0 ≤ 3 * m + 6 := by linarith
  nlinarith [hkey, hpos, mul_nonneg hsnn (by linarith : (0:ℝ) ≤ m + 6)]

/-- The `d = 3` step, in the half-integer form the two crude steps leave:
`3 m^{3/2} - 2 (m-3)^{3/2} ≥ 3m + 6` for `m ≥ 5`. -/
theorem todd_dim_three_core {m : ℝ} (hm : 5 ≤ m) :
    3 * m + 6 ≤ 3 * (m * Real.sqrt m) - 2 * ((m - 3) * Real.sqrt (m - 3)) := by
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hm3 : (0:ℝ) ≤ m - 3 := by linarith
  have hmono : Real.sqrt (m - 3) ≤ Real.sqrt m := Real.sqrt_le_sqrt (by linarith)
  have hsnn : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  -- replace `√(m-3)` by the larger `√m`
  have hstep : 2 * ((m - 3) * Real.sqrt (m - 3)) ≤ 2 * ((m - 3) * Real.sqrt m) := by
    have := mul_le_mul_of_nonneg_left hmono hm3
    linarith
  have hcore := sqrt_core hm
  nlinarith [hcore, hstep, hsnn]

/-! ## The `d = 4` branch, uniform in `m` -/

/-- `2 ≤ m^{2/5}` for `m ≥ 6`, i.e. `32 ≤ m²`. -/
theorem two_le_rpow {m : ℝ} (hm : 6 ≤ m) : (2:ℝ) ≤ m ^ ((2:ℝ) / 5) := by
  have hm0 : (0:ℝ) < m := by linarith
  have h1 : ((32:ℝ)) ^ ((1:ℝ) / 5) ≤ (m ^ (2:ℕ)) ^ ((1:ℝ) / 5) :=
    Real.rpow_le_rpow (by norm_num) (by nlinarith) (by norm_num)
  have h2 : ((32:ℝ)) ^ ((1:ℝ) / 5) = 2 := by
    rw [show (32:ℝ) = (2:ℝ) ^ (5:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 5,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h3 : ((m ^ (2:ℕ) : ℝ)) ^ ((1:ℝ) / 5) = m ^ ((2:ℝ) / 5) := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_mul (le_of_lt hm0)]
    norm_num
  rw [h2, h3] at h1
  exact h1

theorem rpow_eight_fifths {m : ℝ} (hm : 6 ≤ m) : m ^ ((8:ℝ) / 5) ≤ m ^ (2:ℕ) / 2 := by
  have hm0 : (0:ℝ) < m := by linarith
  have h25 := two_le_rpow hm
  have hsplit : m ^ ((8:ℝ) / 5) * m ^ ((2:ℝ) / 5) = m ^ (2:ℕ) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_natCast m 2]
    norm_num
  have hnn : (0:ℝ) ≤ m ^ ((8:ℝ) / 5) := Real.rpow_nonneg (le_of_lt hm0) _
  nlinarith [hsplit, h25, hnn]

/-- **The `d = 4` branch of Todd's arithmetic**, uniform in `m ≥ 6`.  Here `α = log₂ 4 = 2`
exactly and `β = log₂ 3 ≤ 8/5`, so the whole step is polynomial: it reduces to
`m^{2/5} ≥ 2`, that is, to `m² ≥ 32`. -/
theorem todd_dim_four {m : ℝ} (hm : 6 ≤ m) :
    m ^ ((8:ℝ) / 5) + (m - 4) ^ (2:ℕ) / 2 + 2 ≤ m ^ (2:ℕ) := by
  have h := rpow_eight_fifths hm
  nlinarith [h]

/-- `log₂ 3` is squeezed between `3/2` and `8/5`, because `3² ≥ 2³` and `3⁵ ≤ 2⁸`.
These are the only numeric facts the `d = 3` branch needs. -/
theorem logb_three_bounds : (3:ℝ) / 2 ≤ Real.logb 2 3 ∧ Real.logb 2 3 ≤ (8:ℝ) / 5 := by
  constructor
  · rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
    have h : ((2:ℝ) ^ ((3:ℝ) / 2)) ^ (2:ℕ) = 8 := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ ((3:ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    by_contra hc
    push_neg at hc
    have h2 : (3:ℝ) ^ (2:ℕ) ≤ ((2:ℝ) ^ ((3:ℝ) / 2)) ^ (2:ℕ) := by
      gcongr
    rw [h] at h2
    norm_num at h2
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    have h : ((2:ℝ) ^ ((8:ℝ) / 5)) ^ (5:ℕ) = 256 := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ ((8:ℝ) / 5)) 5, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    by_contra hc
    push_neg at hc
    have hnn : (0:ℝ) ≤ (2:ℝ) ^ ((8:ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
    have h5 : ((2:ℝ) ^ ((8:ℝ) / 5)) ^ (5:ℕ) ≤ (3:ℝ) ^ (5:ℕ) := by
      gcongr
    rw [h] at h5
    norm_num at h5

/-! ## An `rpow` toolkit for `log₂` exponents -/

/-- `x ^ log₂ y = y ^ log₂ x`. -/
theorem rpow_logb_swap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ Real.logb 2 y = y ^ Real.logb 2 x := by
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, Real.logb, Real.logb]
  congr 1
  ring

theorem logb_two_pow (k : ℕ) : Real.logb 2 ((2:ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one] <;> norm_num

/-- `(2^k) ^ log₂ D = D ^ k`: powers of two give exact values. -/
theorem pow_two_rpow_logb {D : ℝ} (hD : 0 < D) (k : ℕ) :
    ((2:ℝ) ^ k) ^ Real.logb 2 D = D ^ k := by
  rw [rpow_logb_swap (by positivity) hD, logb_two_pow]
  exact Real.rpow_natCast D k

/-- `3/2 ≤ log₂ D` for `D ≥ 3`. -/
theorem three_halves_le_logb {D : ℝ} (hD : 3 ≤ D) : (3:ℝ) / 2 ≤ Real.logb 2 D :=
  le_trans logb_three_bounds.1 (Real.logb_le_logb_of_le (by norm_num) (by norm_num) hD)

/-- **The `q = 0` branch of Todd's arithmetic**, uniform in `D ≥ 3` and `m ≥ D`. -/
theorem todd_q_zero {D m : ℝ} (hD : 3 ≤ D) (hm : D ≤ m) :
    m ^ Real.logb 2 (D - 1) + 2 ≤ m ^ Real.logb 2 D := by
  have hDpos : (0:ℝ) < D := by linarith
  have hD1 : (2:ℝ) ≤ D - 1 := by linarith
  have hD1pos : (0:ℝ) < D - 1 := by linarith
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  set t : ℝ := Real.logb 2 D with ht
  set β : ℝ := Real.logb 2 (D - 1) with hbeta
  have ht32 : (3:ℝ) / 2 ≤ t := three_halves_le_logb hD
  have hbeta1 : (1:ℝ) ≤ β := by
    have h2 : Real.logb 2 (2:ℝ) = 1 := by rw [Real.logb_self_eq_one] <;> norm_num
    rw [hbeta]
    exact le_trans (le_of_eq h2.symm) (Real.logb_le_logb_of_le (by norm_num) (by norm_num) hD1)
  have hbetat : β ≤ t := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hbeta0 : (0:ℝ) ≤ β := by linarith
  -- the difference is monotone in `m`
  have hmono : D ^ t - D ^ β ≤ m ^ t - m ^ β := by
    have e1 : (0:ℝ) < D ^ β := Real.rpow_pos_of_pos hDpos β
    have e2 : D ^ β ≤ m ^ β := Real.rpow_le_rpow (le_of_lt hDpos) hm hbeta0
    have e3 : D ^ (t - β) ≤ m ^ (t - β) :=
      Real.rpow_le_rpow (le_of_lt hDpos) hm (by linarith)
    have e4 : (1:ℝ) ≤ D ^ (t - β) :=
      Real.one_le_rpow (by linarith) (by linarith)
    have hsplitD : D ^ β * D ^ (t - β) = D ^ t := by
      rw [← Real.rpow_add hDpos]; ring_nf
    have hsplitm : m ^ β * m ^ (t - β) = m ^ t := by
      rw [← Real.rpow_add hmpos]; ring_nf
    nlinarith [e1, e2, e3, e4, hsplitD, hsplitm]
  -- and at `m = D` it is already at least `2`
  have hswap : D ^ β = (D - 1) ^ t := by rw [hbeta, ht, rpow_logb_swap hDpos hD1pos]
  have hbern : 1 + t * (1 / (D - 1)) ≤ (1 + 1 / (D - 1)) ^ t :=
    one_add_mul_self_le_rpow_one_add
      (le_trans (by norm_num) (le_of_lt (one_div_pos.mpr hD1pos))) (by linarith)
  have hratio : (1:ℝ) + 1 / (D - 1) = D / (D - 1) := by field_simp; ring
  have hdiv : (D / (D - 1)) ^ t = D ^ t / (D - 1) ^ t :=
    Real.div_rpow (le_of_lt hDpos) (le_of_lt hD1pos) t
  have hD1t : (0:ℝ) < (D - 1) ^ t := Real.rpow_pos_of_pos hD1pos t
  -- `(D-1)^{t-1} = (D/2)^{log₂(D-1)} ≥ D/2`
  have hexp : (D - 1) ^ (t - 1) = (D / 2) ^ β := by
    have h1 : t - 1 = Real.logb 2 (D / 2) := by
      rw [ht, Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one] <;> norm_num
    rw [h1, hbeta, rpow_logb_swap hD1pos (by linarith)]
  have hge : D / 2 ≤ (D - 1) ^ (t - 1) := by
    rw [hexp]
    calc D / 2 = (D / 2) ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (D / 2) ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hbeta1
  have hsplit1 : (D - 1) ^ (t - 1) * (D - 1) = (D - 1) ^ t := by
    have h1 : (D - 1) ^ (t - 1) * (D - 1) ^ (1:ℝ) = (D - 1) ^ ((t - 1) + 1) :=
      (Real.rpow_add hD1pos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    ring
  have hkey : (D - 1) ^ t + 2 ≤ D ^ t := by
    have hb2 : (D - 1) ^ t * (1 + t * (1 / (D - 1))) ≤ D ^ t := by
      have hmul := mul_le_mul_of_nonneg_left hbern (le_of_lt hD1t)
      rw [hratio, hdiv] at hmul
      field_simp at hmul
      refine le_of_mul_le_mul_left ?_ hD1pos
      have hne : (D:ℝ) - 1 ≠ 0 := ne_of_gt hD1pos
      field_simp
      nlinarith [hmul]
    have hprod : (D - 1) ^ t * (t * (1 / (D - 1))) = t * (D - 1) ^ (t - 1) := by
      field_simp
      rw [← hsplit1]
      ring
    have h94 : (9:ℝ) / 4 ≤ t * (D - 1) ^ (t - 1) := by nlinarith [hge, ht32, hD]
    nlinarith [hb2, hprod, h94]
  calc m ^ β + 2 ≤ m ^ t := by nlinarith [hmono, hswap, hkey]

/-! ## The `q ≥ 1` branch for `D ≥ 4` -/

/-- Since `8 ^ log₂ D = D³`, going out to `m ≥ 8` buys a factor `((D-1)/D)³`. -/
theorem rpow_beta_le {D m : ℝ} (hD : 3 ≤ D) (hm : 8 ≤ m) :
    D ^ (3:ℕ) * m ^ Real.logb 2 (D - 1) ≤ (D - 1) ^ (3:ℕ) * m ^ Real.logb 2 D := by
  have hDpos : (0:ℝ) < D := by linarith
  have hD1pos : (0:ℝ) < D - 1 := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  set t : ℝ := Real.logb 2 D with ht
  set β : ℝ := Real.logb 2 (D - 1) with hbeta
  have hbetat : β ≤ t := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have h8t : ((8:ℝ)) ^ t = D ^ (3:ℕ) := by
    rw [ht, show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num]
    exact pow_two_rpow_logb hDpos 3
  have h8b : ((8:ℝ)) ^ β = (D - 1) ^ (3:ℕ) := by
    rw [hbeta, show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num]
    exact pow_two_rpow_logb hD1pos 3
  have hstep : ((8:ℝ)) ^ (t - β) ≤ m ^ (t - β) :=
    Real.rpow_le_rpow (by norm_num) hm (by linarith)
  have h8split : ((8:ℝ)) ^ β * ((8:ℝ)) ^ (t - β) = ((8:ℝ)) ^ t := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have hmsplit : m ^ β * m ^ (t - β) = m ^ t := by
    rw [← Real.rpow_add hmpos]; ring_nf
  have hmb : (0:ℝ) < m ^ β := Real.rpow_pos_of_pos hmpos β
  have hprod : (D - 1) ^ (3:ℕ) * m ^ β * ((8:ℝ) ^ (t - β))
      ≤ (D - 1) ^ (3:ℕ) * m ^ β * (m ^ (t - β)) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  calc D ^ (3:ℕ) * m ^ β = (D - 1) ^ (3:ℕ) * m ^ β * (8:ℝ) ^ (t - β) := by
        rw [← h8t, ← h8split, h8b]; ring
    _ ≤ (D - 1) ^ (3:ℕ) * m ^ β * m ^ (t - β) := hprod
    _ = (D - 1) ^ (3:ℕ) * m ^ t := by rw [← hmsplit]; ring

/-- **The `q ≥ 1` branch of Todd's arithmetic** for `D ≥ 4` and `m ≥ 8`. -/
theorem todd_q_pos {D m : ℝ} (hD : 4 ≤ D) (hm : 8 ≤ m) (hmD : D ≤ m) :
    m ^ Real.logb 2 (D - 1) + (2 / D) * (m - D) ^ Real.logb 2 D + 2
      ≤ m ^ Real.logb 2 D := by
  have hDpos : (0:ℝ) < D := by linarith
  have hD1pos : (0:ℝ) < D - 1 := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  set t : ℝ := Real.logb 2 D with ht
  set β : ℝ := Real.logb 2 (D - 1) with hbeta
  have ht0 : (0:ℝ) ≤ t := le_trans (by norm_num) (three_halves_le_logb (by linarith))
  have hbetale := rpow_beta_le (by linarith : (3:ℝ) ≤ D) hm
  have hsub : (m - D) ^ t ≤ m ^ t :=
    Real.rpow_le_rpow (by linarith) (by linarith) ht0
  have hmt : (0:ℝ) < m ^ t := Real.rpow_pos_of_pos hmpos t
  have hcube : D ^ (3:ℕ) ≤ m ^ t := by
    have h8t : ((8:ℝ)) ^ t = D ^ (3:ℕ) := by
      rw [ht, show (8:ℝ) = (2:ℝ) ^ (3:ℕ) by norm_num]
      exact pow_two_rpow_logb hDpos 3
    rw [← h8t]
    exact Real.rpow_le_rpow (by norm_num) hm ht0
  have hD3 : (0:ℝ) < D ^ (3:ℕ) := by positivity
  -- clear denominators: the whole step is polynomial in `D` and `m^t`
  rw [← sub_nonneg]
  have hkey : (D ^ (3:ℕ)) * (m ^ t - (m ^ β + 2 / D * (m - D) ^ t + 2)) ≥ 0 := by
    have e1 : D ^ (3:ℕ) * m ^ β ≤ (D - 1) ^ (3:ℕ) * m ^ t := hbetale
    have e2 : D ^ (3:ℕ) * (2 / D * (m - D) ^ t) = 2 * D ^ (2:ℕ) * (m - D) ^ t := by
      field_simp
    have e3 : 2 * D ^ (2:ℕ) * (m - D) ^ t ≤ 2 * D ^ (2:ℕ) * m ^ t := by nlinarith [hsub]
    have e4 : (2:ℝ) ≤ D ^ (2:ℕ) - 3 * D + 1 := by nlinarith [hD]
    have e5 : (D ^ (2:ℕ) - 3 * D + 1) * (D ^ (3:ℕ)) ≤ (D ^ (2:ℕ) - 3 * D + 1) * m ^ t := by
      nlinarith [hcube, e4]
    nlinarith [e1, e2, e3, e5, hD3, hmt]
  nlinarith [hkey, hD3]

/-! ## The `d = 3` branch, uniform in `m` -/

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ ((3:ℝ) / 2) = x * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp [Real.zero_rpow (by norm_num : (3:ℝ)/2 ≠ 0)]
  · rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add h, Real.rpow_one,
      ← Real.sqrt_eq_rpow]

theorem todd_dim_three_core' {m : ℝ} (hm : 5 ≤ m) :
    3 * m + 6 ≤ 3 * m ^ ((3:ℝ) / 2) - 2 * (m - 3) ^ ((3:ℝ) / 2) := by
  have h := todd_dim_three_core hm
  rw [rpow_three_halves (by linarith), rpow_three_halves (by linarith)]
  linarith [h]

set_option maxHeartbeats 1000000 in
/-- **The `d = 3` branch of Todd's arithmetic**, uniform in `m ≥ 5`.  Because
`((m-3)/m)^α ≤ ((m-3)/m)^{3/2}` for `α ≥ 3/2`, the whole step is controlled by the
half-integer statement `3 m^{3/2} - 2 (m-3)^{3/2} ≥ 3m + 6`. -/
theorem todd_dim_three {m : ℝ} (hm : 5 ≤ m) :
    m + (2 / 3) * (m - 3) ^ Real.logb 2 3 + 2 ≤ m ^ Real.logb 2 3 := by
  set α : ℝ := Real.logb 2 3 with hα
  have hα32 : (3:ℝ) / 2 ≤ α := logb_three_bounds.1
  have hm0 : (0:ℝ) < m := by linarith
  have hm3 : (0:ℝ) < m - 3 := by linarith
  have hm1 : (1:ℝ) ≤ m := by linarith
  set r : ℝ := (m - 3) / m with hr
  have hrpos : (0:ℝ) < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hm0]; linarith
  have hbase : r ^ α ≤ r ^ ((3:ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hrpos hr1 hα32
  have hsplitα : (m - 3) ^ α = m ^ α * r ^ α := by
    rw [hr, Real.div_rpow (le_of_lt hm3) (le_of_lt hm0) α]
    field_simp
  have hsplit32 : (m - 3) ^ ((3:ℝ) / 2) = m ^ ((3:ℝ) / 2) * r ^ ((3:ℝ) / 2) := by
    rw [hr, Real.div_rpow (le_of_lt hm3) (le_of_lt hm0) ((3:ℝ) / 2)]
    field_simp
  have hmα : m ^ ((3:ℝ) / 2) ≤ m ^ α := Real.rpow_le_rpow_of_exponent_le hm1 hα32
  have hm32pos : (0:ℝ) < m ^ ((3:ℝ) / 2) := Real.rpow_pos_of_pos hm0 _
  have hcore := todd_dim_three_core' hm
  -- the bracket `1 - (2/3) r^{3/2}` is where all the slack lives
  have hbr : (3:ℝ) * m + 6 ≤ m ^ ((3:ℝ) / 2) * (3 - 2 * r ^ ((3:ℝ) / 2)) := by
    rw [hsplit32] at hcore
    nlinarith [hcore]
  have hbrnn : (0:ℝ) ≤ 3 - 2 * r ^ ((3:ℝ) / 2) := by nlinarith [hbr, hm32pos, hm0]
  have hstep : m ^ α * (3 - 2 * r ^ ((3:ℝ) / 2)) ≥ m ^ ((3:ℝ) / 2) * (3 - 2 * r ^ ((3:ℝ) / 2)) :=
    mul_le_mul_of_nonneg_right hmα hbrnn
  have hrαnn : (0:ℝ) ≤ r ^ α := Real.rpow_nonneg (le_of_lt hrpos) α
  have hmαpos : (0:ℝ) < m ^ α := Real.rpow_pos_of_pos hm0 α
  rw [hsplitα]
  nlinarith [hbase, hstep, hbr, hmαpos, hrαnn]

/-! ## The one remaining case: `d = 5`, `m = 7` -/

theorem logb_two_seven_ge : (14:ℝ) / 5 ≤ Real.logb 2 7 := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  by_contra hc
  push_neg at hc
  have hnn : (0:ℝ) ≤ (2:ℝ) ^ ((14:ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
  have h5 : ((7:ℝ)) ^ (5:ℕ) ≤ ((2:ℝ) ^ ((14:ℝ) / 5)) ^ (5:ℕ) := by gcongr
  have he : ((2:ℝ) ^ ((14:ℝ) / 5)) ^ (5:ℕ) = 16384 := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ ((14:ℝ) / 5)) 5,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [he] at h5
  norm_num at h5

/-- `d = 5`, `m = 7`: the only case not covered by the uniform lemmas. -/
theorem todd_five_seven :
    (7:ℝ) ^ Real.logb 2 4 + (2 / 5) * ((7:ℝ) - 5) ^ Real.logb 2 5 + 2
      ≤ (7:ℝ) ^ Real.logb 2 5 := by
  have h4 : Real.logb 2 (4:ℝ) = 2 := by
    rw [show (4:ℝ) = (2:ℝ) ^ (2:ℕ) by norm_num, logb_two_pow]; norm_num
  have hL : (7:ℝ) ^ Real.logb 2 4 = 49 := by
    rw [h4, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h2 : ((7:ℝ) - 5) ^ Real.logb 2 5 = 5 := by
    rw [show ((7:ℝ) - 5) = 2 by norm_num]
    exact Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  rw [hL, h2]
  have hswap : (7:ℝ) ^ Real.logb 2 5 = (5:ℝ) ^ Real.logb 2 7 :=
    rpow_logb_swap (by norm_num) (by norm_num)
  rw [hswap]
  have hge : (5:ℝ) ^ ((14:ℝ) / 5) ≤ (5:ℝ) ^ Real.logb 2 7 :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) logb_two_seven_ge
  have h53 : (53:ℝ) ≤ (5:ℝ) ^ ((14:ℝ) / 5) := by
    by_contra hc
    push_neg at hc
    have hnn : (0:ℝ) ≤ (5:ℝ) ^ ((14:ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
    have h5 : ((5:ℝ) ^ ((14:ℝ) / 5)) ^ (5:ℕ) ≤ ((53:ℝ)) ^ (5:ℕ) := by gcongr
    have he : ((5:ℝ) ^ ((14:ℝ) / 5)) ^ (5:ℕ) = 6103515625 := by
      rw [← Real.rpow_natCast ((5:ℝ) ^ ((14:ℝ) / 5)) 5,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 5)]
      norm_num
    rw [he] at h5
    norm_num at h5
  linarith

/-! ## The bound as a natural number, and the recursion it satisfies -/

/-- Todd's bound `⌊(n-d)^{log₂ d}⌋`, and `0` when `n ≤ d`. -/
noncomputable def GG (d n : ℕ) : ℕ :=
  if n ≤ d then 0 else ⌊((n : ℝ) - d) ^ Real.logb 2 d⌋₊

theorem GG_of_le {d n : ℕ} (h : n ≤ d) : GG d n = 0 := by simp [GG, h]

theorem GG_of_lt {d n : ℕ} (h : d < n) :
    GG d n = ⌊((n : ℝ) - d) ^ Real.logb 2 d⌋₊ := by
  simp [GG, Nat.not_le.mpr h]

theorem GG_mono (d : ℕ) {m n : ℕ} (h : m ≤ n) : GG d m ≤ GG d n := by
  by_cases hm : m ≤ d
  · simp [GG_of_le hm]
  · have hn : d < n := lt_of_lt_of_le (Nat.not_le.mp hm) h
    rw [GG_of_lt (Nat.not_le.mp hm), GG_of_lt hn]
    refine Nat.floor_le_floor ?_
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · have : (d : ℝ) ≤ m := by exact_mod_cast le_of_lt (Nat.not_le.mp hm)
      linarith
    · have : (m : ℝ) ≤ n := by exact_mod_cast h
      linarith
    · rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · rw [hd0]; simp [Real.logb]
      · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hd0)

set_option maxHeartbeats 1000000 in
/-- **Todd's recursion in `ℕ`**: `2 G(d,⌊n/2⌋) + G(d-1,n-1) + 2 ≤ G(d,n)` for `3 ≤ d`
and `2d ≤ n`. -/
theorem GG_step {d n : ℕ} (hd : 3 ≤ d) (hn : 2 * d ≤ n) :
    2 * GG d (n / 2) + GG (d - 1) (n - 1) + 2 ≤ GG d n := by
  have hdn : d < n := by omega
  set D : ℝ := (d : ℝ) with hD
  have hD3 : (3:ℝ) ≤ D := by rw [hD]; exact_mod_cast hd
  have hDpos : (0:ℝ) < D := by linarith
  set m : ℝ := (n : ℝ) - D with hm
  have hmD : D ≤ m := by
    rw [hm, hD]
    have : ((2 * d : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at this
    linarith
  set α : ℝ := Real.logb 2 D with hα
  set β : ℝ := Real.logb 2 (D - 1) with hβ
  have hαnn : (0:ℝ) ≤ α := Real.logb_nonneg (by norm_num) (by linarith)
  have hβnn : (0:ℝ) ≤ β := Real.logb_nonneg (by norm_num) (by linarith)
  have hmpos : (0:ℝ) < m := by linarith
  -- the two smaller values, as reals
  have hpred : GG (d - 1) (n - 1) = ⌊m ^ β⌋₊ := by
    rw [GG_of_lt (by omega : d - 1 < n - 1), hβ, hm, hD]
    congr 2 <;>
      · push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ d)]
        ring
  have hcast : GG d n = ⌊m ^ α⌋₊ := by rw [GG_of_lt hdn, hα, hm, hD]
  have hqle : ((n / 2 : ℕ) : ℝ) - D ≤ (m - D) / 2 := by
    have h1 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2)
      simpa using this
    rw [hm]
    linarith
  have hexp2 : (2:ℝ) ^ α = D := Real.rpow_logb (by norm_num) (by norm_num) hDpos
  -- the real inequality
  have hreal : 2 * (if n / 2 ≤ d then (0:ℝ) else (((n / 2 : ℕ) : ℝ) - D) ^ α)
      + m ^ β + 2 ≤ m ^ α := by
    by_cases hq : n / 2 ≤ d
    · rw [if_pos hq]
      have := todd_q_zero hD3 hmD
      linarith
    · rw [if_neg hq]
      set q : ℝ := ((n / 2 : ℕ) : ℝ) - D with hqdef
      have hq0 : (0:ℝ) < q := by
        rw [hqdef]
        have : (d : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.not_le.mp hq
        linarith
      have hmd2 : D + 2 ≤ m := by
        have h1 : d + 1 ≤ n / 2 := by omega
        have h2 : ((d : ℝ) + 1) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast h1
        have h3 : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
          have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2)
          simpa using this
        rw [hm]
        linarith
      -- `2 q^α ≤ (2/D) (m-D)^α`
      have hqbound : 2 * q ^ α ≤ (2 / D) * (m - D) ^ α := by
        have h1 : q ^ α ≤ ((m - D) / 2) ^ α :=
          Real.rpow_le_rpow (le_of_lt hq0) hqle hαnn
        have h2 : ((m - D) / 2) ^ α = (m - D) ^ α / D := by
          rw [Real.div_rpow (by linarith) (by norm_num) α, hexp2]
        rw [h2] at h1
        have h3 : (2 / D) * (m - D) ^ α = 2 * ((m - D) ^ α / D) := by ring
        rw [h3]
        linarith [h1]
      have hmn : m = ((n - d : ℕ) : ℝ) := by
        rw [hm, hD]
        push_cast [Nat.cast_sub (le_of_lt hdn)]
        ring
      have hmnge : d + 2 ≤ n - d := by
        have : ((d : ℝ) + 2) ≤ ((n - d : ℕ) : ℝ) := by rw [← hmn]; linarith [hmd2]
        exact_mod_cast this
      have hmain : m ^ β + (2 / D) * (m - D) ^ α + 2 ≤ m ^ α := by
        rcases Nat.lt_or_ge d 4 with hd4 | hd4
        · -- `d = 3`
          have hd3 : d = 3 := by omega
          have hD3' : D = 3 := by rw [hD, hd3]; norm_num
          have hβ0 : β = 1 := by
            rw [hβ, hD3']
            norm_num
          have hmβ : m ^ β = m := by rw [hβ0, Real.rpow_one]
          have hα3 : α = Real.logb 2 3 := by rw [hα, hD3']
          have hm5 : (5:ℝ) ≤ m := by rw [hD3'] at hmd2; linarith
          rw [hmβ, hα3, hD3']
          exact todd_dim_three hm5
        rcases Nat.lt_or_ge d 5 with hd5 | hd5
        · -- `d = 4`
          have hd4' : d = 4 := by omega
          have hD4 : D = 4 := by rw [hD, hd4']; norm_num
          have hα2 : α = 2 := by
            rw [hα, hD4, show (4:ℝ) = (2:ℝ) ^ (2:ℕ) by norm_num, logb_two_pow]; norm_num
          have hβ85 : β ≤ (8:ℝ) / 5 := by
            rw [hβ, hD4, show (4:ℝ) - 1 = (3:ℝ) by norm_num]
            exact logb_three_bounds.2
          have hm1 : (1:ℝ) ≤ m := by linarith
          have hmβ : m ^ β ≤ m ^ ((8:ℝ) / 5) := Real.rpow_le_rpow_of_exponent_le hm1 hβ85
          have hm6 : (6:ℝ) ≤ m := by rw [hD4] at hmd2; linarith
          have h4b := todd_dim_four hm6
          have hcast2 : m ^ α = m ^ (2:ℕ) := by
            rw [hα2, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          have hsubcast : (2 / D) * (m - D) ^ α = (m - 4) ^ (2:ℕ) / 2 := by
            rw [hα2, hD4, show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            ring
          rw [hcast2, hsubcast]
          linarith [hmβ, h4b]
        rcases Nat.lt_or_ge d 6 with hd6 | hd6
        · -- `d = 5`
          have hd5' : d = 5 := by omega
          have hD5 : D = 5 := by rw [hD, hd5']; norm_num
          rcases Nat.lt_or_ge (n - d) 8 with h7 | h8
          · have hm7 : n - d = 7 := by omega
            have hm7' : m = 7 := by rw [hmn, hm7]; norm_num
            rw [hm7', hD5, hα, hβ, hD5, show ((5:ℝ) - 1) = 4 by norm_num]
            exact todd_five_seven
          · have hm8 : (8:ℝ) ≤ m := by
              rw [hmn]
              exact_mod_cast h8
            exact todd_q_pos (by rw [hD5]; norm_num) hm8 (by linarith)
        · -- `d ≥ 6`
          have hD6 : (6:ℝ) ≤ D := by rw [hD]; exact_mod_cast hd6
          have hm8 : (8:ℝ) ≤ m := by linarith
          exact todd_q_pos (by linarith) hm8 (by linarith)
      linarith [hqbound, hmain]
  -- transfer to the floors
  have hXnn : (0:ℝ) ≤ if n / 2 ≤ d then (0:ℝ) else (((n / 2 : ℕ) : ℝ) - D) ^ α := by
    by_cases hq : n / 2 ≤ d
    · simp [hq]
    · rw [if_neg hq]
      exact Real.rpow_nonneg (by
        have : (d : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.not_le.mp hq
        linarith) α
  have hGhalf : (GG d (n / 2) : ℝ)
      ≤ if n / 2 ≤ d then (0:ℝ) else (((n / 2 : ℕ) : ℝ) - D) ^ α := by
    by_cases hq : n / 2 ≤ d
    · simp [GG_of_le hq, hq]
    · rw [if_neg hq, GG_of_lt (Nat.not_le.mp hq), hα, hD]
      exact Nat.floor_le (Real.rpow_nonneg (by
        have : (d : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast Nat.not_le.mp hq
        linarith) _)
  have hGpred : (GG (d - 1) (n - 1) : ℝ) ≤ m ^ β := by
    rw [hpred]
    exact Nat.floor_le (Real.rpow_nonneg (le_of_lt hmpos) β)
  rw [hcast]
  refine Nat.le_floor ?_
  push_cast
  linarith [hreal, hGhalf, hGpred]

/-- `G(d-1, n-1) ≤ G(d, n)`: the facet step never loses. -/
theorem GG_pred {d n : ℕ} (hd : 2 ≤ d) (hdn : d < n) : GG (d - 1) (n - 1) ≤ GG d n := by
  have hm1 : (1:ℝ) ≤ (n : ℝ) - (d : ℝ) := by
    have : ((d : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hpred : GG (d - 1) (n - 1) = ⌊((n : ℝ) - (d : ℝ)) ^ Real.logb 2 ((d : ℝ) - 1)⌋₊ := by
    rw [GG_of_lt (by omega : d - 1 < n - 1)]
    congr 2 <;>
      · push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 1 ≤ d)]
        ring
  rw [hpred, GG_of_lt hdn]
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hm1 ?_)
  refine Real.logb_le_logb_of_le (by norm_num) ?_ (by linarith)
  have : (2:ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- `1 ≤ G(d, n)` when `d ≤ 1 < n`: in dimension at most one the bound is `1`. -/
theorem one_le_GG_of_dim_le_one {d n : ℕ} (hd : d ≤ 1) (hdn : d < n) : 1 ≤ GG d n := by
  rw [GG_of_lt hdn]
  refine Nat.le_floor ?_
  have hexp : Real.logb 2 ((d : ℝ)) = 0 := by
    interval_cases d
    · simp [Real.logb]
    · simp
  rw [hexp, Real.rpow_zero]
  norm_num

/-- `G(2, n) = n - 2`. -/
theorem GG_two {n : ℕ} (hn : 2 < n) : GG 2 n = n - 2 := by
  rw [GG_of_lt hn]
  have hexp : Real.logb 2 ((2:ℕ) : ℝ) = 1 := by
    norm_num
  rw [hexp, Real.rpow_one]
  have hc : ((n : ℝ) - ((2:ℕ) : ℝ)) = ((n - 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  rw [hc, Nat.floor_natCast]

end HirschToddArith

open scoped RealInnerProductSpace
open Hirsch HirschLib HirschWalk HirschFace HirschBridge HirschSimple HirschFacet
open HirschLayer HirschRelax HirschReindex HirschKK HirschKK2 HirschKKb
open HirschShare HirschToddArith LinearOptimization

namespace HirschToddB

set_option maxHeartbeats 4000000 in
/-- **`Δ(d,n) ≤ G(d,n)`.**  Induction on `d + n`; the Kalai--Kleitman recursion is used
only in the range `2d ≤ n`, where Todd's function absorbs it. -/
theorem diamLE_GG : ∀ (N d n : ℕ), d + n ≤ N →
    ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ), DiamLE (Hpoly a b) (GG d n) := by
  intro N
  induction N with
  | zero =>
      intro d n hN a b
      have hd : d = 0 := by omega
      have hn : n = 0 := by omega
      subst hd; subst hn
      rw [GG_of_le (le_refl 0)]
      exact diamLE_of_n_le_d (le_refl 0) a b
  | succ N ih =>
      intro d n hN a b
      by_cases hnd : n ≤ d
      · rw [GG_of_le hnd]
        exact diamLE_of_n_le_d hnd a b
      push_neg at hnd
      by_cases hz : ∃ i, a i = 0
      · obtain ⟨i, hi⟩ := hz
        rcases lt_or_ge (b i) 0 with hb | hb
        · rw [hpoly_eq_empty a b i hi hb]
          exact diamLE_empty _
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [hpoly_drop a b i hi hb]
          exact diamLE_mono _ (GG_mono d (Nat.le_succ k)) (ih d k (by omega) _ _)
      push_neg at hz
      by_cases hd1 : d ≤ 1
      · exact diamLE_mono _ (one_le_GG_of_dim_le_one hd1 hnd) (diamLE_dim_le_one hd1 a b)
      push_neg at hd1
      by_cases hd2 : d = 2
      · subst hd2
        rw [GG_two hnd]
        exact Hirsch.plane_bound_general n a b hz
      have hd3 : 3 ≤ d := by omega
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have hIH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
          DiamLE (Hpoly a' b') (GG (d - 1) k) := fun a' b' => ih (d - 1) k (by omega) a' b'
      have hpred : GG (d - 1) k ≤ GG d (k + 1) := by
        have := GG_pred (by omega : 2 ≤ d) (by omega : d < k + 1)
        simpa using this
      by_cases hfew : k + 1 < 2 * d
      · exact diamLE_mono _ hpred (diamLE_of_few_rows a b hz hfew _ hIH1)
      push_neg at hfew
      have hIH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
          DiamLE (Hpoly (relaxA a F) (relaxB b F)) (GG d ((k + 1) / 2)) := by
        intro F hF
        rw [hpoly_relax_reindex a b F]
        exact diamLE_mono _ (GG_mono d hF) (ih d F.card (by omega) _ _)
      refine diamLE_mono _ ?_
        (kk_recursion' a b hz (GG (d - 1) k) (GG d ((k + 1) / 2)) hIH1 hIH2)
      have hstep := GG_step hd3 hfew
      simp only [Nat.add_sub_cancel] at hstep
      omega

theorem GG_le_target {d n : ℕ} (hdn : d ≤ n) :
    GG d n ≤ ⌊((n : ℝ) - (d : ℝ)) ^ Real.logb 2 d⌋₊ := by
  rcases eq_or_lt_of_le hdn with rfl | h
  · rw [GG_of_le (le_refl d)]
    exact Nat.zero_le _
  · rw [GG_of_lt h]

end HirschToddB

open HirschToddB HirschToddArith

/-- **Todd's bound**: the combinatorial diameter of a `d`-dimensional H-polytope
with `n` facets is at most `(n-d)^{log₂ d}`. -/
theorem solution (d n : ℕ) (hd : 3 ≤ d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (interior (Hpoly a b)).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) ⌊((n : ℝ) - d) ^ (Real.logb 2 d)⌋₊ :=
  HirschKKb.diamLE_mono _ (HirschToddB.GG_le_target hdn)
    (HirschToddB.diamLE_GG (d + n) d n le_rfl a b)
