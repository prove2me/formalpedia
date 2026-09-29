-- Prove2me | solution 1 for LinearOptimization.polyhedron_extreme_point_existence
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T06:10:53.039892+00:00
-- url     : https://prove2.me/submissions/b25bd0e3-4c86-4727-913f-f231dfcc59ed

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.List.TFAE
import Definitions.Def_Polyhedron
import Definitions.Def_ContainsLine
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_lp_active_constraint_equiv
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv

open Matrix LinearOptimization


namespace LOCore

/-- The span of the constraint vectors active at `x`. -/
def activeSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => A i) '' {i | A i ⬝ᵥ x = b i})

lemma mem_polyhedron_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : x ∈ polyhedron A b ↔ ∀ i, b i ≤ A i ⬝ᵥ x := by
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

lemma constraintSet_generalForm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    constraintSet (generalFormSystem A b) = polyhedron A b := by
  ext x
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

/-- Theorem 2.2, specialised to the general-form system at a feasible point:
the active vectors span iff the active system pins `x` down. -/
lemma activeSpan_top_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    activeSpan A b x = ⊤ ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ y = b i) → y = x :=
  (lp_active_constraint_equiv (generalFormSystem A b) x).out 1 2

/-- Theorem 2.2 again: spanning active vectors give a basic solution. -/
lemma isBasicSolution_of_activeSpan_top {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (h : activeSpan A b x = ⊤) :
    IsBasicSolution (generalFormSystem A b) x := by
  refine ⟨fun i hi => absurd hi (by simp [generalFormSystem]), ?_⟩
  exact ((lp_active_constraint_equiv (generalFormSystem A b) x).out 1 0).mp h

/-- The rows of `A` span `ℝⁿ` iff only `0` is annihilated by all of them. -/
lemma rows_span_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ s : Finset (Fin m), s.card = n ∧ LinearIndependent ℝ (fun i : s => A i.1)) ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0 := by
  have h := lp_active_constraint_equiv (fun i => (⟨A i, 0, .ge⟩ : LinearConstraint n)) 0
  have h02 := h.out 0 2
  constructor
  · intro hs
    intro y hy
    refine h02.mp ?_ y ?_
    · obtain ⟨s, hcard, hli⟩ := hs
      exact ⟨s, hcard, fun i _ => by show A i ⬝ᵥ (0 : Fin n → ℝ) = 0; simp, hli⟩
    · intro i _
      exact hy i
  · intro hy
    obtain ⟨s, hcard, -, hli⟩ := h02.mpr (fun y hy' => hy y (fun i => hy' i (by
      show A i ⬝ᵥ (0 : Fin n → ℝ) = 0; simp)))
    exact ⟨s, hcard, hli⟩

/-- Moving along a ray on which the cost strictly decreases makes the LP unbounded. -/
lemma unbounded_of_ray {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) {x e : Fin n → ℝ} (hx : x ∈ polyhedron A b)
    (hray : ∀ i, 0 ≤ A i ⬝ᵥ e) (hc : c ⬝ᵥ e < 0) :
    ∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M := by
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
  · intro i
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    have h2 : 0 ≤ lam * (A i ⬝ᵥ e) := mul_nonneg hlam0 (hray i)
    show b i ≤ A i ⬝ᵥ (x + lam • e)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    linarith
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    exact hlam

/-- The blocking step: from a feasible `x` and a direction `e` that keeps every
active constraint active and is blocked by at least one constraint, we reach a
feasible point whose active constraints span strictly more. -/
lemma block {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {x e : Fin n → ℝ} (hx : x ∈ polyhedron A b)
    (hact : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ e = 0)
    (hS : (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (x + lam • e) ∈ polyhedron A b ∧
      activeSpan A b x < activeSpan A b (x + lam • e) := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => A i ⬝ᵥ e < 0) with hSdef
  have hmemS : ∀ i, i ∈ S ↔ A i ⬝ᵥ e < 0 := by
    intro i; simp [hSdef]
  set f : Fin m → ℝ := fun i => (A i ⬝ᵥ x - b i) / (-(A i ⬝ᵥ e)) with hf
  set lam : ℝ := S.inf' hS f with hlam
  have hlam0 : 0 ≤ lam := by
    refine Finset.le_inf' hS f ?_
    intro i hi
    have hneg : A i ⬝ᵥ e < 0 := (hmemS i).mp hi
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    exact div_nonneg (by linarith) (by linarith)
  obtain ⟨j, hjS, hjeq⟩ := Finset.exists_mem_eq_inf' hS f
  have hlamj : lam = f j := by rw [hlam]; exact hjeq
  have hjneg : A j ⬝ᵥ e < 0 := (hmemS j).mp hjS
  -- feasibility of the new point
  have hfeas : (x + lam • e) ∈ polyhedron A b := by
    intro i
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    show b i ≤ A i ⬝ᵥ (x + lam • e)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases lt_or_ge (A i ⬝ᵥ e) 0 with hneg | hnonneg
    · have hi : i ∈ S := (hmemS i).mpr hneg
      have hle : lam ≤ f i := Finset.inf'_le f hi
      have hpos : 0 < -(A i ⬝ᵥ e) := by linarith
      have hne : -(A i ⬝ᵥ e) ≠ 0 := ne_of_gt hpos
      have hne2 : A i ⬝ᵥ e ≠ 0 := ne_of_lt hneg
      have hval : f i * (-(A i ⬝ᵥ e)) = A i ⬝ᵥ x - b i := by
        exact div_mul_cancel₀ _ hne
      have hmul : lam * (-(A i ⬝ᵥ e)) ≤ A i ⬝ᵥ x - b i := by
        calc lam * (-(A i ⬝ᵥ e)) ≤ f i * (-(A i ⬝ᵥ e)) :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
          _ = A i ⬝ᵥ x - b i := hval
      linarith
    · nlinarith [mul_nonneg hlam0 hnonneg]
  -- previously active constraints stay active
  have hkeep : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ (x + lam • e) = b i := by
    intro i hi
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hact i hi, mul_zero, add_zero]
    exact hi
  -- the blocking constraint j becomes active
  have hjact : A j ⬝ᵥ (x + lam • e) = b j := by
    have hne : A j ⬝ᵥ e ≠ 0 := ne_of_lt hjneg
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hlamj]
    show A j ⬝ᵥ x + ((A j ⬝ᵥ x - b j) / (-(A j ⬝ᵥ e))) * (A j ⬝ᵥ e) = b j
    field_simp
    ring
  -- and its vector was not in the old span
  have hjnot : A j ∉ activeSpan A b x := by
    intro hmem
    have hsub : ((fun i => A i) '' {i | A i ⬝ᵥ x = b i}) ⊆
        {v : Fin n → ℝ | v ⬝ᵥ e = 0} := by
      rintro v ⟨i, hi, rfl⟩
      exact hact i hi
    have hspan : activeSpan A b x ≤
        (⟨⟨⟨{v : Fin n → ℝ | v ⬝ᵥ e = 0}, by
            intro u v hu hv
            simp only [Set.mem_setOf_eq, add_dotProduct] at *
            rw [hu, hv, add_zero]⟩, by simp⟩, by
            intro r v hv
            simp only [Set.mem_setOf_eq, smul_dotProduct] at *
            rw [hv, smul_zero]⟩ : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.span_le.mpr hsub
    have : A j ⬝ᵥ e = 0 := hspan hmem
    linarith
  refine ⟨lam, hlam0, hfeas, lt_of_le_of_ne ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨i, hkeep i hi, rfl⟩
  · intro hEq
    exact hjnot (hEq ▸ Submodule.subset_span ⟨j, hjact, rfl⟩)



/-- **Descent to a basic feasible solution.** If the rows of `A` span `ℝⁿ` (equivalently,
`P` contains no line), then from any feasible point we can reach a basic feasible solution
of no greater cost — unless the cost is unbounded below on `P`. -/
lemma descent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hspan : ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0) :
    ∀ (k : ℕ) (x : Fin n → ℝ), x ∈ polyhedron A b →
      n - Module.finrank ℝ (activeSpan A b x) ≤ k →
      (∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M) ∨
      (∃ y, IsBasicFeasibleSolution (generalFormSystem A b) y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
  classical
  have hfrn : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hbfs : ∀ z : Fin n → ℝ, z ∈ polyhedron A b → activeSpan A b z = ⊤ →
      IsBasicFeasibleSolution (generalFormSystem A b) z := by
    intro z hz htop
    exact ⟨isBasicSolution_of_activeSpan_top A b z htop, by
      rw [constraintSet_generalForm]; exact hz⟩
  intro k
  induction k with
  | zero =>
      intro x hx hk
      right
      have hle : Module.finrank ℝ (activeSpan A b x) ≤ n := by
        have h := Submodule.finrank_le (activeSpan A b x)
        rw [hfrn] at h
        exact h
      have heq : Module.finrank ℝ (activeSpan A b x) = Module.finrank ℝ (Fin n → ℝ) := by
        rw [hfrn]; omega
      exact ⟨x, hbfs x hx (Submodule.eq_top_of_finrank_eq heq), le_refl _⟩
  | succ k ih =>
      intro x hx hk
      by_cases htop : activeSpan A b x = ⊤
      · exact Or.inr ⟨x, hbfs x hx htop, le_refl _⟩
      -- a direction along which every active constraint stays active
      obtain ⟨y0, hy0, hy0ne⟩ : ∃ y : Fin n → ℝ,
          (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ y = b i) ∧ y ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact htop ((activeSpan_top_iff A b x).mpr (fun y hy => hcon y hy))
      set d : Fin n → ℝ := y0 - x with hd
      have hdne : d ≠ 0 := sub_ne_zero.mpr hy0ne
      have hdact : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ d = 0 := by
        intro i hi
        rw [hd, dotProduct_sub, hy0 i hi, hi, sub_self]
      obtain ⟨i₀, hi₀⟩ : ∃ i, A i ⬝ᵥ d ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hdne (hspan d hcon)
      -- one descent step, given a usable direction
      have step : ∀ e : Fin n → ℝ, (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ e = 0) →
          (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty → c ⬝ᵥ e ≤ 0 →
          (∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M) ∨
          (∃ y, IsBasicFeasibleSolution (generalFormSystem A b) y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
        intro e hacte hSe hce
        obtain ⟨lam, hlam0, hfeas, hlt⟩ := block A b hx hacte hSe
        have hrank : Module.finrank ℝ (activeSpan A b x) <
            Module.finrank ℝ (activeSpan A b (x + lam • e)) :=
          Submodule.finrank_lt_finrank_of_lt hlt
        have hk' : n - Module.finrank ℝ (activeSpan A b (x + lam • e)) ≤ k := by omega
        rcases ih (x + lam • e) hfeas hk' with h | ⟨y, hy, hcy⟩
        · exact Or.inl h
        · refine Or.inr ⟨y, hy, ?_⟩
          have hmono : c ⬝ᵥ (x + lam • e) ≤ c ⬝ᵥ x := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            have : lam * (c ⬝ᵥ e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hce
            linarith
          linarith
      -- unboundedness when the ray is never blocked
      have ray : ∀ e : Fin n → ℝ, ¬ (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty →
          ∀ i, 0 ≤ A i ⬝ᵥ e := by
        intro e hSe i
        by_contra hcon
        push_neg at hcon
        exact hSe ⟨i, by simp [hcon]⟩
      have hnegdot : ∀ (v : Fin n → ℝ) (i : Fin m), A i ⬝ᵥ (-v) = -(A i ⬝ᵥ v) := by
        intro v i; rw [dotProduct_neg]
      have hdactneg : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ (-d) = 0 := by
        intro i hi; rw [hnegdot, hdact i hi, neg_zero]
      rcases lt_trichotomy (c ⬝ᵥ d) 0 with hc | hc | hc
      · by_cases hS : (Finset.univ.filter (fun i => A i ⬝ᵥ d < 0)).Nonempty
        · exact step d hdact hS (le_of_lt hc)
        · exact Or.inl (unbounded_of_ray A b c hx (ray d hS) hc)
      · -- the cost is flat along `d`; move in whichever direction is blocked
        rcases lt_or_gt_of_ne hi₀ with hlt | hgt
        · refine step d hdact ⟨i₀, by simp [hlt]⟩ (le_of_eq hc)
        · refine step (-d) hdactneg ⟨i₀, by simp [hnegdot, hgt]⟩ ?_
          rw [dotProduct_neg, hc, neg_zero]
      · have hcneg : c ⬝ᵥ (-d) < 0 := by rw [dotProduct_neg]; linarith
        by_cases hS : (Finset.univ.filter (fun i => A i ⬝ᵥ (-d) < 0)).Nonempty
        · exact step (-d) hdactneg hS (le_of_lt hcneg)
        · exact Or.inl (unbounded_of_ray A b c hx (ray (-d) hS) hcneg)

end LOCore


open LOCore

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty) :
    List.TFAE
      [ (Set.extremePoints ℝ (polyhedron A b)).Nonempty,
        ¬ ContainsLine (polyhedron A b),
        ∃ s : Finset (Fin m), s.card = n ∧
          LinearIndependent ℝ (fun i : s => A i.1) ] := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  -- A polyhedron contains a line exactly when some nonzero direction is killed by every row.
  have hline : ContainsLine (polyhedron A b) ↔ ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ i, A i ⬝ᵥ d = 0 := by
    constructor
    · rintro ⟨z, hz, d, hd0, hd⟩
      refine ⟨d, hd0, fun i => ?_⟩
      by_contra hcon
      -- pick a scalar driving the `i`-th constraint below its bound
      obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, A i ⬝ᵥ z + lam * (A i ⬝ᵥ d) < b i := by
        rcases lt_or_gt_of_ne hcon with h | h
        · refine ⟨(b i - 1 - A i ⬝ᵥ z) / (A i ⬝ᵥ d), ?_⟩
          rw [div_mul_cancel₀ _ (ne_of_lt h)]; linarith
        · refine ⟨(b i - 1 - A i ⬝ᵥ z) / (A i ⬝ᵥ d), ?_⟩
          rw [div_mul_cancel₀ _ (ne_of_gt h)]; linarith
      have hmem : b i ≤ A i ⬝ᵥ (z + lam • d) := hd lam i
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hmem
      linarith
    · rintro ⟨d, hd0, hd⟩
      refine ⟨x₀, hx₀, d, hd0, fun lam i => ?_⟩
      have h1 : b i ≤ A i ⬝ᵥ x₀ := hx₀ i
      show b i ≤ A i ⬝ᵥ (x₀ + lam • d)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hd i, mul_zero, add_zero]
      exact h1
  have hspan_iff : (¬ ContainsLine (polyhedron A b)) ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0 := by
    rw [hline]
    constructor
    · intro h y hy
      by_contra hy0
      exact h ⟨y, hy0, hy⟩
    · rintro h ⟨d, hd0, hd⟩
      exact hd0 (h d hd)
  tfae_have 1 → 2 := by
    rintro ⟨x, hx⟩
    rw [hspan_iff]
    intro y hy
    by_contra hy0
    -- `x ± y` are both feasible and `x` is their midpoint
    have hfeas : ∀ t : ℝ, x + t • y ∈ polyhedron A b := by
      intro t i
      have h1 : b i ≤ A i ⬝ᵥ x := hx.1 i
      show b i ≤ A i ⬝ᵥ (x + t • y)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hy i, mul_zero, add_zero]
      exact h1
    have hmid : x ∈ openSegment ℝ (x + (1:ℝ) • y) (x + (-1:ℝ) • y) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := hx.2 (hfeas 1) (hfeas (-1)) hmid
    have hy1 : (1:ℝ) • y = 0 := by
      have := congrArg (fun z => z - x) this
      simpa using this
    exact hy0 (by simpa using hy1)
  tfae_have 2 → 3 := by
    intro h2
    exact (rows_span_iff A).mpr (hspan_iff.mp h2)
  tfae_have 3 → 2 := by
    intro h3
    exact hspan_iff.mpr ((rows_span_iff A).mp h3)
  tfae_have 3 → 1 := by
    intro h3
    have hspan := (rows_span_iff A).mp h3
    have hd := descent A b 0 hspan n x₀ hx₀ (Nat.sub_le _ _)
    rcases hd with hunb | ⟨y, hy, -⟩
    · exfalso
      obtain ⟨w, -, hw⟩ := hunb 0
      rw [zero_dotProduct] at hw
      exact lt_irrefl _ hw
    · refine ⟨y, ?_⟩
      have hymem : y ∈ constraintSet (generalFormSystem A b) := hy.2
      have hnec : (constraintSet (generalFormSystem A b)).Nonempty := ⟨y, hymem⟩
      have hthm := lp_vertex_extreme_bfs_equiv (generalFormSystem A b) y hnec hymem
      have := (hthm.out 2 1).mp hy
      rwa [constraintSet_generalForm] at this
  tfae_finish
