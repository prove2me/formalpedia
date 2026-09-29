-- Prove2me | solution 1 for MarkovMixing.tv_eq_half_l1
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:49:32.664135+00:00
-- url     : https://prove2.me/submissions/0ec31cb4-a807-45d9-81d5-5048e76b6067

import Definitions.Def_mm_mixing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (μ ν : V → ℝ) (hμ : IsDist μ) (hν : IsDist ν) :
    tvDist μ ν = 2⁻¹ * ∑ x, |μ x - ν x| ∧
    tvDist μ ν = ∑ x ∈ Finset.univ.filter (fun x : V => ν x ≤ μ x), (μ x - ν x) := by
  classical
  set p : V → Prop := fun x => ν x ≤ μ x with hp
  set B : Finset V := Finset.univ.filter p with hB
  set s : ℝ := ∑ x ∈ B, (μ x - ν x) with hs
  have hzero : ∑ x, (μ x - ν x) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hν.2, sub_self]
  have hsplit : ∑ x ∈ B, (μ x - ν x)
      + ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x) = 0 := by
    rw [hB, Finset.sum_filter_add_sum_filter_not Finset.univ p (fun x => μ x - ν x)]
    exact hzero
  have hcompl : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x) = -s := by
    rw [hs]; linarith [hsplit]
  have hBnn : ∀ x ∈ B, 0 ≤ μ x - ν x := by
    intro x hx
    rw [hB, Finset.mem_filter] at hx
    linarith [hx.2]
  have hBcnp : ∀ x ∈ Finset.univ.filter (fun x => ¬ p x), μ x - ν x ≤ 0 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have := hx.2
    rw [hp] at this
    push_neg at this
    linarith
  have hs_nonneg : 0 ≤ s := by
    rw [hs]
    exact Finset.sum_nonneg hBnn
  -- the ℓ¹ identity
  have hl1 : ∑ x, |μ x - ν x| = 2 * s := by
    have hsp := Finset.sum_filter_add_sum_filter_not Finset.univ p (fun x => |μ x - ν x|)
    have h1 : ∑ x ∈ B, |μ x - ν x| = s := by
      rw [hs, hB]
      exact Finset.sum_congr rfl fun x hx => abs_of_nonneg (hBnn x (by rw [hB]; exact hx))
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), |μ x - ν x| = s := by
      have : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), |μ x - ν x|
          = ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), -(μ x - ν x) :=
        Finset.sum_congr rfl fun x hx => abs_of_nonpos (hBcnp x hx)
      rw [this, Finset.sum_neg_distrib, hcompl, neg_neg]
    rw [← hsp, hB] at *
    linarith [h1, h2]
  -- the supremum is attained at `B`
  have hbdd : BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    Set.Finite.bddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have hupper : ∀ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ s := by
    intro A
    have hrw : ∑ x ∈ A, μ x - ∑ x ∈ A, ν x = ∑ x ∈ A, (μ x - ν x) := by
      rw [Finset.sum_sub_distrib]
    rw [hrw, abs_le]
    have hAsp := Finset.sum_filter_add_sum_filter_not A p (fun x => μ x - ν x)
    have hA1 : ∑ x ∈ A.filter p, (μ x - ν x) ≤ s := by
      rw [hs]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => hBnn x hx)
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hB, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hx.2⟩
    have hA1nn : 0 ≤ ∑ x ∈ A.filter p, (μ x - ν x) :=
      Finset.sum_nonneg fun x hx => hBnn x (by
        rw [Finset.mem_filter] at hx
        rw [hB, Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hx.2⟩)
    have hA2np : ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) ≤ 0 :=
      Finset.sum_nonpos fun x hx => hBcnp x (by
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ x, hx.2⟩)
    have hA2ge : -s ≤ ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) := by
      rw [← hcompl]
      have hsub : ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (μ x - ν x)
          ≤ ∑ x ∈ A.filter (fun x => ¬ p x), (μ x - ν x) := by
        have hneg : ∑ x ∈ A.filter (fun x => ¬ p x), (-(μ x - ν x))
            ≤ ∑ x ∈ Finset.univ.filter (fun x => ¬ p x), (-(μ x - ν x)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x hx _ => ?_)
          · intro x hx
            rw [Finset.mem_filter] at hx
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ x, hx.2⟩
          · have := hBcnp x hx
            linarith
        rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib] at hneg
        linarith
      linarith
    constructor <;> linarith [hAsp, hA1, hA1nn, hA2np, hA2ge]
  have hattain : |∑ x ∈ B, μ x - ∑ x ∈ B, ν x| = s := by
    have hrw : ∑ x ∈ B, μ x - ∑ x ∈ B, ν x = s := by
      rw [hs, Finset.sum_sub_distrib]
    rw [hrw, abs_of_nonneg hs_nonneg]
  have htv : tvDist μ ν = s := by
    refine le_antisymm (ciSup_le hupper) ?_
    rw [← hattain]
    exact le_ciSup hbdd B
  exact ⟨by rw [htv, hl1]; ring, by rw [htv, hs, hB]⟩
