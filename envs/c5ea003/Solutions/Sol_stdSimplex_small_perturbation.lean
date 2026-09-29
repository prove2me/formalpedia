-- Prove2me | solution 1 for stdSimplex_small_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T17:23:27.358972+00:00
-- url     : https://prove2.me/submissions/11b1e43b-7c75-47f1-afdb-c97b2ac79ad1

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open Set

/-!
Lattimore--Szepesvari, *Bandit Algorithms*, Theorem 37.12, Step 1,
printed p.490: a strictly positive probability vector may be perturbed a
sufficiently small distance in either direction along any zero-sum vector.
-/

theorem stdSimplex_small_perturbation
    {d : ℕ} (u q : Fin d → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin d))
    (hupos : ∀ i, 0 < u i) (hq : ∑ i, q i = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ →
      (fun i ↦ u i + Δ * q i) ∈ stdSimplex ℝ (Fin d) := by
  classical
  have hd : 0 < d := by
    by_contra hd0
    have : d = 0 := Nat.eq_zero_of_not_pos hd0
    subst d
    simpa [stdSimplex] using hu.2
  let ratios : Finset ℝ :=
    Finset.univ.image (fun i : Fin d ↦ u i / (|q i| + 1))
  have hratios : ratios.Nonempty := by
    apply Finset.image_nonempty.mpr
    exact ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  let δ : ℝ := ratios.min' hratios
  have hδpos : 0 < δ := by
    apply (Finset.lt_min'_iff ratios hratios).2
    intro r hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    exact div_pos (hupos i) (by positivity)
  refine ⟨δ, hδpos, ?_⟩
  intro Δ hΔ
  refine ⟨?_, ?_⟩
  · intro i
    have hδi : δ ≤ u i / (|q i| + 1) := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hΔi : |Δ| ≤ u i / (|q i| + 1) := hΔ.trans hδi
    have hden : 0 < |q i| + 1 := by positivity
    have hmul : |Δ| * (|q i| + 1) ≤ u i := by
      exact (le_div_iff₀ hden).mp hΔi
    have habsΔ : -|Δ| ≤ Δ := neg_abs_le Δ
    have habsq : -|q i| ≤ q i := neg_abs_le (q i)
    have hprod : -( |Δ| * |q i| ) ≤ Δ * q i := by
      have hp := neg_abs_le (Δ * q i)
      rwa [abs_mul] at hp
    nlinarith [abs_nonneg Δ, abs_nonneg (q i)]
  · calc
      (∑ i, (u i + Δ * q i)) = (∑ i, u i) + Δ * ∑ i, q i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 1 := by rw [hu.2, hq]; ring

theorem solution
    {d : ℕ} (u q : Fin d → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin d))
    (hupos : ∀ i, 0 < u i) (hq : ∑ i, q i = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Δ : ℝ, |Δ| ≤ δ →
      (fun i ↦ u i + Δ * q i) ∈ stdSimplex ℝ (Fin d) :=
  stdSimplex_small_perturbation u q hu hupos hq
