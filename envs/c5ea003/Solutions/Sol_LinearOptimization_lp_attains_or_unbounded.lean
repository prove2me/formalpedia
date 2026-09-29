-- Prove2me | solution 1 for LinearOptimization.lp_attains_or_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T06:27:16.769918+00:00
-- url     : https://prove2.me/submissions/9e67c8b6-e9a3-425b-aa87-0bf77783766c

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.List.TFAE
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.EReal.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Finite.Lattice
import Definitions.Def_Polyhedron
import Definitions.Def_ContainsLine
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_active_constraint_equiv
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_basic_solutions_finite
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence

open Matrix LinearOptimization


namespace LOCore2

/-- The span of the constraint vectors active at `x`. -/
def actSpan {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) (x : Fin n → ℝ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => (C i).a) '' {i | (C i).IsActiveAt x})

/-- Constraint families with no `≤` constraint. -/
def NoLe {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) : Prop :=
  ∀ i, (C i).rel ≠ ConstraintRel.le

lemma ge_of_mem {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (i : ι) : (C i).b ≤ (C i).a ⬝ᵥ x := by
  have h := hx i
  rcases hr : (C i).rel with _ | _ | _
  · simp only [LinearConstraint.IsSatisfiedAt, hr] at h; exact h
  · exact absurd hr (hC i)
  · simp only [LinearConstraint.IsSatisfiedAt, hr] at h; exact le_of_eq h.symm

lemma eq_active_of_mem {ι : Type} {n : ℕ} {C : ι → LinearConstraint n}
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (i : ι)
    (hi : (C i).rel = ConstraintRel.eq) : (C i).IsActiveAt x := by
  have h := hx i
  simp only [LinearConstraint.IsSatisfiedAt, hi] at h
  exact h

lemma mem_of_ge {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {y : Fin n → ℝ} (h1 : ∀ i, (C i).b ≤ (C i).a ⬝ᵥ y)
    (h2 : ∀ i, (C i).rel = ConstraintRel.eq → (C i).a ⬝ᵥ y = (C i).b) :
    y ∈ constraintSet C := by
  intro i
  rcases hr : (C i).rel with _ | _ | _
  · simp only [LinearConstraint.IsSatisfiedAt, hr]; exact h1 i
  · exact absurd hr (hC i)
  · simp only [LinearConstraint.IsSatisfiedAt, hr]; exact h2 i hr

/-- Theorem 2.2: spanning active vectors at a feasible point give a basic feasible solution. -/
lemma isBFS_of_actSpan_top {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n}
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) (h : actSpan C x = ⊤) :
    IsBasicFeasibleSolution C x :=
  ⟨⟨fun i hi => eq_active_of_mem hx i hi,
    ((lp_active_constraint_equiv C x).out 1 0).mp h⟩, hx⟩

/-- Moving along a ray on which the cost strictly decreases makes the LP unbounded. -/
lemma unbounded_of_ray {ι : Type} {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (c : Fin n → ℝ) {x e : Fin n → ℝ} (hx : x ∈ constraintSet C)
    (hray : ∀ i, 0 ≤ (C i).a ⬝ᵥ e)
    (hactzero : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0)
    (hc : c ⬝ᵥ e < 0) :
    ∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M := by
  intro M
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ c ⬝ᵥ x + lam * (c ⬝ᵥ e) < M := by
    refine ⟨max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1), le_max_left _ _, ?_⟩
    have hpos : 0 < -(c ⬝ᵥ e) := by linarith
    have hge : (c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1 ≤ max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) :=
      le_max_right _ _
    have hkey : (c ⬝ᵥ x - M) < ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) * (-(c ⬝ᵥ e)) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hpos)]
      linarith
    nlinarith [hge, hpos]
  refine ⟨x + lam • e, ?_, ?_⟩
  · refine mem_of_ge hC ?_ ?_
    · intro i
      have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
      have h2 : 0 ≤ lam * ((C i).a ⬝ᵥ e) := mul_nonneg hlam0 (hray i)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      linarith
    · intro i hi
      have hia : (C i).IsActiveAt x := eq_active_of_mem hx i hi
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hactzero i hia, mul_zero, add_zero]
      exact hia
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    exact hlam

/-- The blocking step. -/
lemma block {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    {x e : Fin n → ℝ} (hx : x ∈ constraintSet C)
    (hact : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0)
    (hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (x + lam • e) ∈ constraintSet C ∧
      actSpan C x < actSpan C (x + lam • e) := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0) with hSdef
  have hmemS : ∀ i, i ∈ S ↔ (C i).a ⬝ᵥ e < 0 := by intro i; simp [hSdef]
  set f : ι → ℝ := fun i => ((C i).a ⬝ᵥ x - (C i).b) / (-((C i).a ⬝ᵥ e)) with hf
  set lam : ℝ := S.inf' hS f with hlam
  have hlam0 : 0 ≤ lam := by
    refine Finset.le_inf' hS f ?_
    intro i hi
    have hneg : (C i).a ⬝ᵥ e < 0 := (hmemS i).mp hi
    have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
    exact div_nonneg (by linarith) (by linarith)
  obtain ⟨j, hjS, hjeq⟩ := Finset.exists_mem_eq_inf' hS f
  have hlamj : lam = f j := by rw [hlam]; exact hjeq
  have hjneg : (C j).a ⬝ᵥ e < 0 := (hmemS j).mp hjS
  -- previously active constraints stay active
  have hkeep : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ (x + lam • e) = (C i).b := by
    intro i hi
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hact i hi, mul_zero, add_zero]
    exact hi
  have hgeall : ∀ i, (C i).b ≤ (C i).a ⬝ᵥ (x + lam • e) := by
    intro i
    have h1 : (C i).b ≤ (C i).a ⬝ᵥ x := ge_of_mem hC hx i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases lt_or_ge ((C i).a ⬝ᵥ e) 0 with hneg | hnonneg
    · have hi : i ∈ S := (hmemS i).mpr hneg
      have hle : lam ≤ f i := Finset.inf'_le f hi
      have hpos : 0 < -((C i).a ⬝ᵥ e) := by linarith
      have hne : -((C i).a ⬝ᵥ e) ≠ 0 := ne_of_gt hpos
      have hval : f i * (-((C i).a ⬝ᵥ e)) = (C i).a ⬝ᵥ x - (C i).b := div_mul_cancel₀ _ hne
      have hmul : lam * (-((C i).a ⬝ᵥ e)) ≤ (C i).a ⬝ᵥ x - (C i).b := by
        calc lam * (-((C i).a ⬝ᵥ e)) ≤ f i * (-((C i).a ⬝ᵥ e)) :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
          _ = (C i).a ⬝ᵥ x - (C i).b := hval
      linarith
    · nlinarith [mul_nonneg hlam0 hnonneg]
  have hfeas : (x + lam • e) ∈ constraintSet C := by
    refine mem_of_ge hC hgeall ?_
    intro i hi
    exact hkeep i (eq_active_of_mem hx i hi)
  -- the blocking constraint becomes active
  have hjact : (C j).a ⬝ᵥ (x + lam • e) = (C j).b := by
    have hne : (C j).a ⬝ᵥ e ≠ 0 := ne_of_lt hjneg
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hlamj]
    show (C j).a ⬝ᵥ x
        + (((C j).a ⬝ᵥ x - (C j).b) / (-((C j).a ⬝ᵥ e))) * ((C j).a ⬝ᵥ e) = (C j).b
    field_simp
    ring
  have hjnot : (C j).a ∉ actSpan C x := by
    intro hmem
    have hsub : ((fun i => (C i).a) '' {i | (C i).IsActiveAt x}) ⊆
        {v : Fin n → ℝ | v ⬝ᵥ e = 0} := by
      rintro v ⟨i, hi, rfl⟩
      exact hact i hi
    have hspan : actSpan C x ≤
        (⟨⟨⟨{v : Fin n → ℝ | v ⬝ᵥ e = 0}, by
            intro u v hu hv
            simp only [Set.mem_setOf_eq, add_dotProduct] at *
            rw [hu, hv, add_zero]⟩, by simp⟩, by
            intro r v hv
            simp only [Set.mem_setOf_eq, smul_dotProduct] at *
            rw [hv, smul_zero]⟩ : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.span_le.mpr hsub
    have : (C j).a ⬝ᵥ e = 0 := hspan hmem
    linarith
  refine ⟨lam, hlam0, hfeas, lt_of_le_of_ne ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨i, hkeep i hi, rfl⟩
  · intro hEq
    exact hjnot (hEq ▸ Submodule.subset_span ⟨j, hjact, rfl⟩)

/-- **Descent to a basic feasible solution**, for any `≤`-free constraint family whose
constraint vectors span `ℝⁿ`. -/
lemma descent {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (c : Fin n → ℝ) (hspan : ∀ y : Fin n → ℝ, (∀ i, (C i).a ⬝ᵥ y = 0) → y = 0) :
    ∀ (k : ℕ) (x : Fin n → ℝ), x ∈ constraintSet C →
      n - Module.finrank ℝ (actSpan C x) ≤ k →
      (∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M) ∨
      (∃ y, IsBasicFeasibleSolution C y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
  classical
  have hfrn : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  intro k
  induction k with
  | zero =>
      intro x hx hk
      right
      have hle : Module.finrank ℝ (actSpan C x) ≤ n := by
        have h := Submodule.finrank_le (actSpan C x)
        rw [hfrn] at h
        exact h
      have heq : Module.finrank ℝ (actSpan C x) = Module.finrank ℝ (Fin n → ℝ) := by
        rw [hfrn]; omega
      exact ⟨x, isBFS_of_actSpan_top hx (Submodule.eq_top_of_finrank_eq heq), le_refl _⟩
  | succ k ih =>
      intro x hx hk
      by_cases htop : actSpan C x = ⊤
      · exact Or.inr ⟨x, isBFS_of_actSpan_top hx htop, le_refl _⟩
      obtain ⟨y0, hy0, hy0ne⟩ : ∃ y : Fin n → ℝ,
          (∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ y = (C i).b) ∧ y ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact htop (((lp_active_constraint_equiv C x).out 1 2).mpr (fun y hy => hcon y hy))
      set d : Fin n → ℝ := y0 - x with hd
      have hdne : d ≠ 0 := sub_ne_zero.mpr hy0ne
      have hdact : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ d = 0 := by
        intro i hi
        have h1 : (C i).a ⬝ᵥ x = (C i).b := hi
        rw [hd, dotProduct_sub, hy0 i hi, h1, sub_self]
      obtain ⟨i₀, hi₀⟩ : ∃ i, (C i).a ⬝ᵥ d ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hdne (hspan d hcon)
      have step : ∀ e : Fin n → ℝ, (∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ e = 0) →
          (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty → c ⬝ᵥ e ≤ 0 →
          (∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M) ∨
          (∃ y, IsBasicFeasibleSolution C y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
        intro e hacte hSe hce
        obtain ⟨lam, hlam0, hfeas, hlt⟩ := block hC hx hacte hSe
        have hrank : Module.finrank ℝ (actSpan C x) <
            Module.finrank ℝ (actSpan C (x + lam • e)) :=
          Submodule.finrank_lt_finrank_of_lt hlt
        have hk' : n - Module.finrank ℝ (actSpan C (x + lam • e)) ≤ k := by omega
        rcases ih (x + lam • e) hfeas hk' with h | ⟨y, hy, hcy⟩
        · exact Or.inl h
        · refine Or.inr ⟨y, hy, ?_⟩
          have hmono : c ⬝ᵥ (x + lam • e) ≤ c ⬝ᵥ x := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            have : lam * (c ⬝ᵥ e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hce
            linarith
          linarith
      have ray : ∀ e : Fin n → ℝ, ¬ (Finset.univ.filter (fun i => (C i).a ⬝ᵥ e < 0)).Nonempty →
          ∀ i, 0 ≤ (C i).a ⬝ᵥ e := by
        intro e hSe i
        by_contra hcon
        push_neg at hcon
        exact hSe ⟨i, by simp [hcon]⟩
      have hdactneg : ∀ i, (C i).IsActiveAt x → (C i).a ⬝ᵥ (-d) = 0 := by
        intro i hi; rw [dotProduct_neg, hdact i hi, neg_zero]
      rcases lt_trichotomy (c ⬝ᵥ d) 0 with hc | hc | hc
      · by_cases hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ d < 0)).Nonempty
        · exact step d hdact hS (le_of_lt hc)
        · exact Or.inl (unbounded_of_ray hC c hx (ray d hS) hdact hc)
      · rcases lt_or_gt_of_ne hi₀ with hlt | hgt
        · exact step d hdact ⟨i₀, by simp [hlt]⟩ (le_of_eq hc)
        · refine step (-d) hdactneg ⟨i₀, by simp [dotProduct_neg, hgt]⟩ ?_
          rw [dotProduct_neg, hc, neg_zero]
      · have hcneg : c ⬝ᵥ (-d) < 0 := by rw [dotProduct_neg]; linarith
        by_cases hS : (Finset.univ.filter (fun i => (C i).a ⬝ᵥ (-d) < 0)).Nonempty
        · exact step (-d) hdactneg hS (le_of_lt hcneg)
        · exact Or.inl (unbounded_of_ray hC c hx (ray (-d) hS) hdactneg hcneg)

/-- The descent applied with zero cost: a nonempty feasible set whose constraint
vectors span `ℝⁿ` contains a basic feasible solution. -/
lemma exists_bfs {ι : Type} [Fintype ι] {n : ℕ} {C : ι → LinearConstraint n} (hC : NoLe C)
    (hspan : ∀ y : Fin n → ℝ, (∀ i, (C i).a ⬝ᵥ y = 0) → y = 0)
    {x : Fin n → ℝ} (hx : x ∈ constraintSet C) :
    ∃ y, IsBasicFeasibleSolution C y := by
  rcases descent hC 0 hspan n x hx (Nat.sub_le _ _) with h | ⟨y, hy, -⟩
  · obtain ⟨w, -, hw⟩ := h 0
    rw [zero_dotProduct] at hw
    exact absurd hw (lt_irrefl _)
  · exact ⟨y, hy⟩

end LOCore2


open LOCore2

/-- Every linear functional on `Fin n → ℝ` is `v ↦ v ⬝ᵥ d` for some `d`. -/
private lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual ℝ (Fin n → ℝ)) :
    ∃ d : Fin n → ℝ, ∀ v, f v = v ⬝ᵥ d := by
  classical
  refine ⟨fun j => f (Pi.single j 1), fun v => ?_⟩
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ)) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  calc f v = f (∑ j, v j • (Pi.single j (1 : ℝ))) := by rw [← hv]
    _ = ∑ j, v j * f (Pi.single j 1) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; simp [smul_eq_mul]
    _ = v ⬝ᵥ (fun j => f (Pi.single j 1)) := rfl

/-- If only `0` is orthogonal to every element of `S`, then `S` spans. -/
private lemma span_eq_top_of_orth {n : ℕ} (S : Set (Fin n → ℝ))
    (h : ∀ v : Fin n → ℝ, (∀ w ∈ S, w ⬝ᵥ v = 0) → v = 0) : Submodule.span ℝ S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨d, hd⟩ := dual_eq_dotProduct f
  have hzero : ∀ w ∈ S, w ⬝ᵥ d = 0 := by
    intro w hw
    have h1 : f w ∈ Submodule.map f (Submodule.span ℝ S) :=
      Submodule.mem_map_of_mem (Submodule.subset_span hw)
    rw [hfmap, Submodule.mem_bot] at h1
    rw [← hd]; exact h1
  exact hf0 (LinearMap.ext fun v => by simp [hd v, h d hzero])

/-- The lineality space of `{x | Ax ≥ b}`: directions killed by every row. -/
private def lineality {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Submodule ℝ (Fin n → ℝ) where
  carrier := {d | ∀ i, A i ⬝ᵥ d = 0}
  add_mem' := by intro u v hu hv i; rw [dotProduct_add, hu i, hv i, add_zero]
  zero_mem' := by intro i; simp
  smul_mem' := by intro r v hv i; rw [dotProduct_smul, hv i, smul_zero]

/-- The orthogonal complement of a subspace with respect to the dot product. -/
private def perp {n : ℕ} (W : Submodule ℝ (Fin n → ℝ)) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ w ∈ W, w ⬝ᵥ v = 0}
  add_mem' := by intro u v hu hv w hw; rw [dotProduct_add, hu w hw, hv w hw, add_zero]
  zero_mem' := by intro w hw; simp
  smul_mem' := by intro r v hv w hw; rw [dotProduct_smul, hv w hw, smul_zero]

private lemma sup_perp_eq_top {n : ℕ} (W : Submodule ℝ (Fin n → ℝ)) : W ⊔ perp W = ⊤ := by
  have h : Submodule.span ℝ ((W ⊔ perp W : Submodule ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)) = ⊤ := by
    refine span_eq_top_of_orth _ ?_
    intro v hv
    have hvW : v ∈ perp W := fun w hw => hv w (Submodule.mem_sup_left hw)
    have hvv : v ⬝ᵥ v = 0 := hv v (Submodule.mem_sup_right hvW)
    exact dotProduct_self_eq_zero.mp hvv
  rwa [Submodule.span_eq] at h

private lemma lpValue_eq_bot {n : ℕ} (c : Fin n → ℝ) (S : Set (Fin n → ℝ))
    (h : ∀ M : ℝ, ∃ w ∈ S, c ⬝ᵥ w < M) : lpValue c S = ⊥ := by
  have hexr : ∀ y : EReal, ⊥ < y → ∃ r : ℝ, ((r : EReal)) ≤ y := by
    intro y
    induction y using EReal.rec with
    | bot => intro hy; exact absurd hy (lt_irrefl _)
    | coe t => intro _; exact ⟨t, le_rfl⟩
    | top => intro _; exact ⟨0, le_top⟩
  rw [lpValue]
  refine iInf_eq_bot.mpr ?_
  intro y hy
  obtain ⟨r, hry⟩ := hexr y hy
  obtain ⟨w, hw, hlt⟩ := h r
  refine ⟨w, ?_⟩
  have hred : (⨅ _ : w ∈ S, ((c ⬝ᵥ w : ℝ) : EReal)) = ((c ⬝ᵥ w : ℝ) : EReal) := by simp [hw]
  rw [hred]
  calc ((c ⬝ᵥ w : ℝ) : EReal) < ((r : ℝ) : EReal) := by exact_mod_cast hlt
    _ ≤ y := hry

private lemma constraintSet_generalForm' {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : constraintSet (generalFormSystem A b) = polyhedron A b := by
  ext x
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hne : (polyhedron A b).Nonempty) :
    lpValue c (polyhedron A b) = ⊥ ∨ ∃ x, IsLpOptimal c (polyhedron A b) x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  set L : Submodule ℝ (Fin n → ℝ) := lineality A with hL
  have hmemL : ∀ d, d ∈ L ↔ ∀ i, A i ⬝ᵥ d = 0 := fun d => Iff.rfl
  by_cases hcL : ∃ d ∈ L, c ⬝ᵥ d ≠ 0
  · -- the cost varies along a line contained in `P`, so it is unbounded below
    left
    obtain ⟨d, hdL, hcd⟩ := hcL
    -- replace `d` by `-d` if necessary so that the cost strictly decreases
    obtain ⟨e, heL, hce⟩ : ∃ e ∈ L, c ⬝ᵥ e < 0 := by
      rcases lt_or_gt_of_ne hcd with h | h
      · exact ⟨d, hdL, h⟩
      · refine ⟨-d, Submodule.neg_mem _ hdL, ?_⟩
        rw [dotProduct_neg]; linarith
    have hx₀c : x₀ ∈ constraintSet (generalFormSystem A b) := by
      rwa [constraintSet_generalForm']
    have hC : NoLe (generalFormSystem A b) := by intro i; simp [generalFormSystem]
    have hray : ∀ i, 0 ≤ (generalFormSystem A b i).a ⬝ᵥ e := by
      intro i
      show (0:ℝ) ≤ A i ⬝ᵥ e
      rw [(hmemL e).mp heL i]
    have hactzero : ∀ i, (generalFormSystem A b i).IsActiveAt x₀ →
        (generalFormSystem A b i).a ⬝ᵥ e = 0 := by
      intro i _
      exact (hmemL e).mp heL i
    have hunb := unbounded_of_ray hC c hx₀c hray hactzero hce
    refine lpValue_eq_bot c _ ?_
    intro M
    obtain ⟨w, hw, hlt⟩ := hunb M
    exact ⟨w, by rwa [constraintSet_generalForm'] at hw, hlt⟩
  · -- the cost is constant along every line, so we may restrict to `L^⊥`
    push_neg at hcL
    -- a finite basis of the lineality space
    set p : ℕ := Module.finrank ℝ ↥L with hp
    set bas : Module.Basis (Fin p) ℝ ↥L := Module.finBasis ℝ ↥L with hbas
    set g : Fin p → (Fin n → ℝ) := fun k => ((bas k : ↥L) : Fin n → ℝ) with hg
    have hgL : ∀ k, g k ∈ L := fun k => (bas k).2
    have hgspan : Submodule.span ℝ (Set.range g) = L := by
      have hcomp : g = (L.subtype : ↥L →ₗ[ℝ] (Fin n → ℝ)) ∘ (bas : Fin p → ↥L) := rfl
      rw [hcomp, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]
    -- the augmented system: `Ax ≥ b` together with `g_k' x = 0`
    set C : (Fin m ⊕ Fin p) → LinearConstraint n := fun i =>
      match i with
      | .inl i => ⟨A i, b i, ConstraintRel.ge⟩
      | .inr k => ⟨g k, 0, ConstraintRel.eq⟩ with hC
    have hCnole : NoLe C := by rintro (i | k) <;> simp [hC]
    have hsubP : ∀ x, x ∈ constraintSet C → x ∈ polyhedron A b := by
      intro x hx i
      exact hx (Sum.inl i)
    -- the augmented constraint vectors span `ℝⁿ`
    have hspanC : ∀ y : Fin n → ℝ, (∀ i, (C i).a ⬝ᵥ y = 0) → y = 0 := by
      intro y hy
      have hyL : y ∈ L := fun i => hy (Sum.inl i)
      have hyperp : ∀ w ∈ L, w ⬝ᵥ y = 0 := by
        intro w hw
        rw [← hgspan] at hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro v ⟨k, rfl⟩; exact hy (Sum.inr k)
        · simp
        · intro u v _ _ hu hv; rw [add_dotProduct, hu, hv, add_zero]
        · intro r v _ hv; rw [smul_dotProduct, hv, smul_zero]
      exact dotProduct_self_eq_zero.mp (hyperp y hyL)
    -- every feasible point can be pushed into `L^⊥` at the same cost
    have hpush : ∀ x, x ∈ polyhedron A b → ∃ r, r ∈ constraintSet C ∧ c ⬝ᵥ r = c ⬝ᵥ x := by
      intro x hx
      have hxtop : x ∈ (⊤ : Submodule ℝ (Fin n → ℝ)) := Submodule.mem_top
      rw [← sup_perp_eq_top L, Submodule.mem_sup] at hxtop
      obtain ⟨l, hl, r, hr, hsum⟩ := hxtop
      have hrx : r = x - l := by rw [← hsum]; ring
      refine ⟨r, ?_, ?_⟩
      · intro i
        cases i with
        | inl i =>
            have h1 : b i ≤ A i ⬝ᵥ x := hx i
            show b i ≤ A i ⬝ᵥ r
            rw [hrx, dotProduct_sub, (hmemL l).mp hl i, sub_zero]
            exact h1
        | inr k =>
            show g k ⬝ᵥ r = 0
            exact hr (g k) (hgL k)
      · rw [hrx, dotProduct_sub, hcL l hl, sub_zero]
    obtain ⟨r₀, hr₀, -⟩ := hpush x₀ hx₀
    by_cases hunb : ∀ M : ℝ, ∃ w ∈ constraintSet C, c ⬝ᵥ w < M
    · left
      refine lpValue_eq_bot c _ ?_
      intro M
      obtain ⟨w, hw, hlt⟩ := hunb M
      exact ⟨w, hsubP w hw, hlt⟩
    · right
      have hfin : {y | IsBasicFeasibleSolution C y}.Finite :=
        (lp_basic_solutions_finite C).2
      have hbfsne : ∃ y, IsBasicFeasibleSolution C y := by
        rcases descent hCnole c hspanC n r₀ hr₀ (Nat.sub_le _ _) with h | ⟨y, hy, -⟩
        · exact absurd h hunb
        · exact ⟨y, hy⟩
      set F : Finset (Fin n → ℝ) := hfin.toFinset with hF
      have hmemF : ∀ y, y ∈ F ↔ IsBasicFeasibleSolution C y := by
        intro y; rw [hF, Set.Finite.mem_toFinset]; rfl
      have hFne : F.Nonempty := by
        obtain ⟨y, hy⟩ := hbfsne
        exact ⟨y, (hmemF y).mpr hy⟩
      obtain ⟨w, hwF, hwmin⟩ := F.exists_min_image (fun y => c ⬝ᵥ y) hFne
      have hwBFS : IsBasicFeasibleSolution C w := (hmemF w).mp hwF
      refine ⟨w, hsubP w hwBFS.2, ?_⟩
      intro y hy
      obtain ⟨r, hr, hcr⟩ := hpush y hy
      rcases descent hCnole c hspanC n r hr (Nat.sub_le _ _) with h | ⟨z, hz, hcz⟩
      · exact absurd h hunb
      · have hle : c ⬝ᵥ w ≤ c ⬝ᵥ z := hwmin z ((hmemF z).mpr hz)
        linarith
