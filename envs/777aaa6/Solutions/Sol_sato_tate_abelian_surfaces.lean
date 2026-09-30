-- Prove2me | solution 1 for sato_tate_abelian_surfaces
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T04:51:09.567143+00:00
-- url     : https://prove2.me/submissions/3b5f95b6-100d-495e-8f72-7313deb6b0ad

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Filter

private def cutoff (n : ℕ) : ℕ := 2 * (n + 2)

private theorem cutoff_not_prime (n : ℕ) : ¬ Nat.Prime (cutoff n) :=
  Nat.not_prime_mul (by decide) (by omega)

private theorem cutoff_count (n : ℕ) :
    Nat.primeCounting (cutoff n) = ((Finset.range (cutoff n)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ,
    if_neg (cutoff_not_prime n), Nat.add_zero, Nat.count_eq_card_filter_range]

private theorem cutoff_count_ne (n : ℕ) : (Nat.primeCounting (cutoff n) : ℝ) ≠ 0 := by
  have h : Nat.primeCounting (cutoff n) ≠ 0 := by
    rw [ne_eq, Nat.primeCounting_eq_zero_iff]
    dsimp [cutoff]
    omega
  exact_mod_cast h

private theorem cutoff_tendsto : Tendsto (fun n => (cutoff n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop.mpr
  intro b
  exact eventually_atTop.mpr ⟨b, fun n hn => by dsimp [cutoff]; omega⟩

theorem solution : ¬ (∀ (A B : ℤ) (C D : ℤ),
    ∃ (density : ℝ → ℝ), ∀ alpha beta : ℝ, alpha ≤ beta →
      Tendsto (fun x : ℝ =>
        (∑ p ∈ (Finset.range (Nat.floor x)).filter Nat.Prime,
          if alpha ≤ (A + B : ℝ) / (2 * Real.sqrt p) ∧
              (A + B : ℝ) / (2 * Real.sqrt p) ≤ beta
          then (1 : ℝ) else 0) /
          (Nat.primeCounting (Nat.floor x) : ℝ))
        atTop (nhds (∫ t in alpha..beta, density t))) := by
  intro h
  obtain ⟨density, hd⟩ := h 0 0 0 0
  have hz : Tendsto (fun x : ℝ =>
      (((Finset.range (Nat.floor x)).filter Nat.Prime).card : ℝ) /
        (Nat.primeCounting (Nat.floor x) : ℝ)) atTop (nhds 0) := by
    simpa using hd 0 0 le_rfl
  have hc := hz.comp cutoff_tendsto
  have he : (fun n : ℕ =>
      (((Finset.range (Nat.floor (cutoff n : ℝ))).filter Nat.Prime).card : ℝ) /
        (Nat.primeCounting (Nat.floor (cutoff n : ℝ)) : ℝ)) = fun _ => (1 : ℝ) := by
    funext n
    rw [Nat.floor_natCast, ← cutoff_count n, div_self (cutoff_count_ne n)]
  change Tendsto (fun n : ℕ =>
      (((Finset.range (Nat.floor (cutoff n : ℝ))).filter Nat.Prime).card : ℝ) /
        (Nat.primeCounting (Nat.floor (cutoff n : ℝ)) : ℝ)) atTop (nhds 0) at hc
  rw [he] at hc
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hc
  norm_num at h10

#print axioms solution
