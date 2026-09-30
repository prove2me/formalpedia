-- Prove2me | solution 1 for Hirsch.spindle_one_step
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T14:49:19.921393+00:00
-- url     : https://prove2.me/submissions/013e0274-d74a-4352-9fda-9b56b4ed16a4

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_spindle_one_step_from_apex_facet

open scoped RealInnerProductSpace
open Set Hirsch

/-- An extreme point of a positive-dimensional H-polytope is tight at some inequality. -/
lemma extreme_exists_tight (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ i, ⟪a i, x⟫ = b i := by
  haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  by_contra h
  push Not at h
  have hxP : x ∈ Hpoly a b := hx.1
  have hlt : ∀ i, ⟪a i, x⟫ < b i := fun i => lt_of_le_of_ne (hxP i) (h i)
  let y : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ)
  have hy0 : y ≠ 0 := by
    intro hy
    have : (1 : ℝ) = 0 := by
      simpa [y, PiLp.single_eq_same] using
        congrArg (fun z : EuclideanSpace ℝ (Fin d) => z ⟨0, hd⟩) hy
    norm_num at this
  have hop : x ∈ openSegment ℝ (x - y) (x + y) :=
    mem_openSegment_sub_add (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) x y
  -- Scale y down so both endpoints lie in P.
  let C : ℝ := ∑ i, |⟪a i, y⟫|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let δ : ℝ := Finset.univ.inf' (Finset.univ_nonempty) (fun i => b i - ⟪a i, x⟫)
  have hδ : 0 < δ := by
    obtain ⟨i0, _, hδeq⟩ :=
      Finset.univ.exists_mem_eq_inf' Finset.univ_nonempty (fun i => b i - ⟪a i, x⟫)
    have : 0 < b i0 - ⟪a i0, x⟫ := sub_pos.2 (hlt i0)
    simpa [δ, hδeq] using this
  let ε : ℝ := δ / (2 * (C + 1))
  have hεpos : 0 < ε := div_pos hδ (by positivity)
  have hmem (σ : ℝ) (hσ : |σ| = ε) : x + σ • y ∈ Hpoly a b := by
    intro i
    have : ⟪a i, x + σ • y⟫ = ⟪a i, x⟫ + σ * ⟪a i, y⟫ := by
      simp [inner_add_right, inner_smul_right]
    rw [this]
    have hslack : δ ≤ b i - ⟪a i, x⟫ :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have habs : |σ * ⟪a i, y⟫| ≤ ε * C := by
      have : |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by simp [abs_mul, hσ]
      have : |⟪a i, y⟫| ≤ C :=
        Finset.single_le_sum (f := fun j : Fin n => |⟪a j, y⟫|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      calc
        |σ * ⟪a i, y⟫| = ε * |⟪a i, y⟫| := by simp [abs_mul, hσ]
        _ ≤ ε * C := mul_le_mul_of_nonneg_left this hεpos.le
    have : σ * ⟪a i, y⟫ ≤ |σ * ⟪a i, y⟫| := le_abs_self _
    have : ε * C ≤ δ / 2 := by
      have : ε * (C + 1) = δ / 2 := by
        dsimp [ε]
        field_simp
      have : C ≤ C + 1 := by linarith
      nlinarith
    linarith
  have hp1 : x + ε • y ∈ Hpoly a b := hmem ε (abs_of_pos hεpos)
  have hp2 : x - ε • y ∈ Hpoly a b := by
    simpa [sub_eq_add_neg, neg_smul] using hmem (-ε) (by simp [abs_of_pos hεpos])
  have hop' : x ∈ openSegment ℝ (x - ε • y) (x + ε • y) :=
    mem_openSegment_sub_add (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) x (ε • y)
  have heq : x - ε • y = x := hx.2 hp2 hp1 hop'
  have : ε • y = 0 := by
    have := congrArg (fun z => z + ε • y) heq
    simpa using this
  exact hy0 ((smul_eq_zero.1 this).resolve_left hεpos.ne')

theorem solution (d n : ℕ) (hd : 0 < d) (hn : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1)))
      (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      u' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      v' ∈ Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, u'⟫ = b' i) ↔ ⟪a' i, v'⟫ ≠ b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin (d + 1)),
        ¬ (w 0 = u' ∧ w (d + 1) = v' ∧
            ∀ j < d + 1, w j = w (j + 1) ∨
              Adj (Hpoly a' b') (w j) (w (j + 1))) := by
  have hnpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hn
  obtain ⟨i0, htight⟩ := extreme_exists_tight d n hd hnpos a b hu
  exact spindle_one_step_from_apex_facet d n hd hn a b u v i0 hne hbd hu hv
    hspindle htight hlong
