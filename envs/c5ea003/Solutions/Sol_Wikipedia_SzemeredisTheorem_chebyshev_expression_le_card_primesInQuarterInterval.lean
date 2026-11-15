-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.chebyshev_expression_le_card_primesInQuarterInterval
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:34.966171+00:00
-- url     : https://prove2.me/submissions/099ce4ee-8579-465e-bbf2-667162cfd841

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics



@[simp]
theorem mem_primesInQuarterInterval {X p : ℕ} :
    p ∈ primesInQuarterInterval X ↔
      p.Prime ∧ X / 4 < p ∧ p ≤ X := by
  simp [primesInQuarterInterval, and_left_comm, and_comm]

/-- The interval finset is the difference of the two standard prime
finsets supplied by `Mathlib.NumberTheory.PrimeCounting`. -/
theorem primesInQuarterInterval_eq_sdiff (X : ℕ) :
    primesInQuarterInterval X =
      Nat.primesLE X \ Nat.primesLE (X / 4) := by
  ext p
  rw [mem_primesInQuarterInterval, Finset.mem_sdiff,
    Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hqp, hpX⟩
    exact ⟨⟨hpX, hp⟩, fun h ↦ by omega⟩
  · rintro ⟨⟨hpX, hp⟩, hnot⟩
    refine ⟨hp, ?_, hpX⟩
    by_contra! hpq
    exact hnot ⟨hpq, hp⟩







/-- The theta mass in `(X / 4, X]` is the sum of `log p` over the interval
finset. -/
theorem theta_sub_theta_quarter_eq_sum (X : ℕ) :
    Chebyshev.theta X -
        Chebyshev.theta ((X / 4 : ℕ) : ℝ) =
      ∑ p ∈ primesInQuarterInterval X, log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log,
    primesInQuarterInterval_eq_sdiff]
  rw [sub_eq_iff_eq_add]
  exact (Finset.sum_sdiff (f := fun p : ℕ ↦ log p)
    (Nat.primesLE_mono (Nat.div_le_self X 4))).symm

/-- Each logarithmic prime weight in `(X / 4, X]` is at most `log X`. -/
theorem theta_sub_theta_quarter_le_card_mul_log (X : ℕ) :
    Chebyshev.theta X -
        Chebyshev.theta ((X / 4 : ℕ) : ℝ) ≤
      (#(primesInQuarterInterval X) : ℝ) * log X := by
  rw [theta_sub_theta_quarter_eq_sum]
  calc
    (∑ p ∈ primesInQuarterInterval X, log p)
        ≤ ∑ _p ∈ primesInQuarterInterval X, log X := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log
        (by exact_mod_cast (mem_primesInQuarterInterval.mp hp).1.pos)
        (by exact_mod_cast (mem_primesInQuarterInterval.mp hp).2.2)
    _ = (#(primesInQuarterInterval X) : ℝ) * log X := by simp

















end Wikipedia.SzemeredisTheorem

end
open Wikipedia.SzemeredisTheorem
open Finset Real
open Filter Asymptotics

open Wikipedia.SzemeredisTheorem in
/-- An explicit Chebyshev-expression lower bound for the number of primes in
`(X / 4, X]`.  The numerator has positive linear main term; its other terms
are elementary logarithmic and square-root errors. -/
theorem solution
    {X : ℕ} (hX : 2 ≤ X) :
    (((X : ℝ) * log 2 - log (X + 1) -
          2 * √(X : ℝ) * log X) -
        log 4 * (X / 4 : ℕ)) /
      log X ≤
        (#(primesInQuarterInterval X) : ℝ) := by
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hX))
  rw [div_le_iff₀ hlogX]
  calc
    ((X : ℝ) * log 2 - log (X + 1) -
          2 * √(X : ℝ) * log X) -
        log 4 * (X / 4 : ℕ)
        ≤ Chebyshev.theta X -
            Chebyshev.theta ((X / 4 : ℕ) : ℝ) := by
      have hlo := Chebyshev.theta_ge X
      have hup := Chebyshev.theta_le_log4_mul_x
        (x := ((X / 4 : ℕ) : ℝ)) (by positivity)
      linarith
    _ ≤ (#(primesInQuarterInterval X) : ℝ) * log X :=
      theta_sub_theta_quarter_le_card_mul_log X
