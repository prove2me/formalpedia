-- Prove2me | solution 1 for KServer.binary_kernel_of_atom_balance
-- status  : ACCEPTED   (prove)
-- author  : @kwal0203
-- created : 2026-10-30T17:04:43.669773+00:00
-- url     : https://prove2.me/submissions/fb0b02d7-4540-46ae-9bc8-6ae8519d34a9

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem solution {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (H : Ω → ℕ)
    (B : Ω → Bool) (u v q : Ω → ℝ)
    (hknown : ∀ ω ω', H ω = H ω' → u ω = u ω' ∧ v ω = v ω' ∧ q ω = q ω')
    (hbalance : ∀ ω₀,
      (∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀ ∧ B ω = true), P ω) =
        q ω₀ * (∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀), P ω)) :
    ∀ f : ℝ → ℝ,
      (∑ ω, P ω * f (if B ω then u ω else v ω)) =
        ∑ ω, P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω)) := by
  classical
  intro f
  have hatom (ω₀ : Ω) :
      (∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀),
        P ω * f (if B ω then u ω else v ω)) =
      ∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀),
        P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω)) := by
    let A := Finset.univ.filter (fun ω => H ω = H ω₀)
    have hknown' (ω : Ω) (hω : ω ∈ A) := hknown ω ω₀ (Finset.mem_filter.mp hω).2
    have hleft : (∑ ω ∈ A.filter (fun ω => B ω = true), P ω) = q ω₀ * ∑ ω ∈ A, P ω := by
      simpa only [A, Finset.filter_filter, Bool.and_eq_true] using hbalance ω₀
    have hright : (∑ ω ∈ A.filter (fun ω => ¬ B ω = true), P ω) =
        (1 - q ω₀) * ∑ ω ∈ A, P ω := by
      have hsplit := Finset.sum_filter_add_sum_filter_not A (fun ω => B ω = true) P
      linarith
    change (∑ ω ∈ A, P ω * f (if B ω then u ω else v ω)) =
      ∑ ω ∈ A, P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω))
    rw [← Finset.sum_filter_add_sum_filter_not A (fun ω => B ω = true)
      (fun ω => P ω * f (if B ω then u ω else v ω))]
    have hl : (∑ ω ∈ A.filter (fun ω => B ω = true),
        P ω * f (if B ω then u ω else v ω)) =
        (∑ ω ∈ A.filter (fun ω => B ω = true), P ω) * f (u ω₀) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      obtain ⟨hA, hB⟩ := Finset.mem_filter.mp hω
      simp [hB, (hknown' ω hA).1]
    have hr : (∑ ω ∈ A.filter (fun ω => ¬ B ω = true),
        P ω * f (if B ω then u ω else v ω)) =
        (∑ ω ∈ A.filter (fun ω => ¬ B ω = true), P ω) * f (v ω₀) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      obtain ⟨hA, hB⟩ := Finset.mem_filter.mp hω
      simp [hB, (hknown' ω hA).2.1]
    have hc : (∑ ω ∈ A, P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω))) =
        (∑ ω ∈ A, P ω) * (q ω₀ * f (u ω₀) + (1 - q ω₀) * f (v ω₀)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [(hknown' ω hω).1, (hknown' ω hω).2.1, (hknown' ω hω).2.2]
    rw [hl, hr, hc, hleft, hright]
    ring
  let I := Finset.univ.image H
  have hmap : ∀ ω ∈ (Finset.univ : Finset Ω), H ω ∈ I := by
    intro ω hω
    exact Finset.mem_image.mpr ⟨ω, hω, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
      (fun ω => P ω * f (if B ω then u ω else v ω)),
    ← Finset.sum_fiberwise_of_maps_to hmap
      (fun ω => P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω)))]
  apply Finset.sum_congr rfl
  intro h hh
  obtain ⟨ω₀, _, rfl⟩ := Finset.mem_image.mp hh
  exact hatom ω₀
