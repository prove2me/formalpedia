-- Prove2me | solution 1 for Hirsch.relaxation_no_new_neighbours
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:03:37.211259+00:00
-- url     : https://prove2.me/submissions/59b3bb59-f7b8-4036-8314-378198cd1a3e

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Hirsch

/-!
# Dropping inequalities creates no new neighbours

Relaxing an H-polyhedron by deleting the inequalities a vertex's neighbourhood does not
touch leaves that neighbourhood unchanged.  The proof follows a putative new edge out of
the vertex and stops where it first leaves the original polyhedron: that exit point is the
far endpoint of a genuine edge, hence a vertex touching a deleted inequality.
-/

namespace HirschAux

variable {d n : ℕ}

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

/-- An H-polytope is closed: it is an intersection of closed half-spaces. -/
theorem hpoly_closed (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    IsClosed (Hpoly a b) := by
  have : Hpoly a b = ⋂ i, {x : EuclideanSpace ℝ (Fin d) | ⟪a i, x⟫ ≤ b i} := by
    ext x; simp [Hpoly, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le (continuous_const.inner continuous_id) continuous_const

section Walks

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

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

end Walks

/-- The set of inequalities tight at a point. -/
noncomputable def tightSet (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ⟪a i, x⟫ = b i)

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

theorem relaxA_of_mem (a : Fin n → EuclideanSpace ℝ (Fin d)) (F : Finset (Fin n))
    {j : Fin n} (hj : j ∈ F) : relaxA a F j = a j := by simp [relaxA, hj]

theorem relaxB_of_mem (b : Fin n → ℝ) (F : Finset (Fin n)) {j : Fin n} (hj : j ∈ F) :
    relaxB b F j = b j := by simp [relaxB, hj]

/-- Cutting an extreme subset down to a smaller ambient set keeps it extreme. -/
theorem isExtreme_inter {E : Type*} [AddCommGroup E] [Module ℝ E] {Q T S : Set E}
    (h : IsExtreme ℝ Q T) (hSQ : S ⊆ Q) : IsExtreme ℝ S (S ∩ T) := by
  constructor
  · exact Set.inter_subset_left
  · intro x1 h1 x2 h2 z hz hsg
    exact ⟨h1, h.2 (hSQ h1) (hSQ h2) hz.2 hsg⟩

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

end HirschAux

open HirschAux

/-- **Dropping untouched inequalities creates no new neighbours.**  Let `P` be the
H-polyhedron cut out by `⟪a i, x⟫ ≤ b i`, let `x` be a vertex of `P` all of whose tight
inequalities are indexed by `F`, and suppose every neighbour of `x` in `P` also has all
its tight inequalities in `F`.  Then every neighbour of `x` in the polyhedron cut out by
the inequalities of `F` alone already lies in `P`. -/
theorem solution (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Finset (Fin n)) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b))
    (hFx : ∀ i : Fin n, ⟪a i, x⟫ = b i → i ∈ F)
    (hadj : Adj (Hpoly (fun i => if i ∈ F then a i else 0)
      (fun i => if i ∈ F then b i else 1)) x y)
    (hnb : ∀ w, Adj (Hpoly a b) x w → ∀ i : Fin n, ⟪a i, w⟫ = b i → i ∈ F) :
    y ∈ Hpoly a b := by
  classical
  refine HirschAux.adj_relax_reflect a b F hx ?_ hadj ?_
  · intro i hi
    exact hFx i (Finset.mem_filter.mp hi).2
  · intro w hw i hi
    exact hnb w hw i (Finset.mem_filter.mp hi).2
