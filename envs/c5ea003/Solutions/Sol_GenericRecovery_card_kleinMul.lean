-- Prove2me | solution 1 for GenericRecovery.card_kleinMul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:18:02.110716+00:00
-- url     : https://prove2.me/submissions/3a40549d-274a-4011-af1a-f6b57215bbf8

-- Sol generated from Combinatorics/GenericRecoveryHintSymmetry.lean
import Mathlib
import Definitions.Def_Combinatorics_GenericRecoveryHintSymmetry
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
import Theorems.Thm_GenericRecovery_two_pow_dvd_two_mul
import Theorems.Thm_GenericRecovery_zmod_eq_iff
/-
# GENERIC-RECOVERY, cycle III: every hint deficit is a symmetry

Cycles I and II established that a `t`-bit hint reduces the search by exactly
`2^t`, that the bound is attained, and that two special families — value hints
and trace hints — fall short by one and by three bits respectively.  Cycle III
asks *why* a family falls short, and answers: **because the hint is invariant
under a group of candidate symmetries, and the deficit is the order of that
group.**

* `GenericRecovery.cost_ge_of_family` — the abstract mechanism: an injective
  family of candidates carrying the same hint reading forces a class at least
  that large.
* `GenericRecovery.card_image_mul_le`, `GenericRecovery.worstCost_ge_of_uniform`
  — if such a family exists at *every* candidate, the number of usable readings
  drops by the factor `g`: `g · #readings ≤ |S|`, i.e. `log₂ g` bits are lost
  from the hint's nominal budget.
* `GenericRecovery.kleinMul`, `GenericRecovery.card_kleinMul`,
  `GenericRecovery.kleinMul_sq_eq_one` — the invariance group of the trace hint:
  the Klein four-group `{±1, ±(1 + 2^{t-1})}` of square roots of `1` mod `2^t`.
* `GenericRecovery.cost_sqHint_ge_four`, `GenericRecovery.card_image_sqHint_le`
  — the payoff: on *any* candidate set of units closed under that group, the
  square (equivalently trace) hint has classes of size at least `4` and at most
  `|S|/4` readings.  Cycle II computed `4` on the full odd-residue set; here the
  same deficit is derived from structure and holds on every symmetric candidate
  set, e.g. the sparse prime sets of the experiment.
-/

open GenericRecovery

open Finset

/-! ## 1.  The abstract mechanism -/

variable {α β ι : Type*} [DecidableEq β]




/-! ## 2.  The invariance group of the trace hint -/


variable (n : ℕ)


theorem not_dvd_two : ¬ (2:ℤ) ^ (n + 3) ∣ 2 := by
  intro h
  have hle := Int.le_of_dvd (by norm_num) h
  have hlt : (2:ℤ) ^ 3 ≤ 2 ^ (n + 3) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hlt
  omega

theorem not_dvd_two_pow_pred : ¬ (2:ℤ) ^ (n + 3) ∣ (2:ℤ) ^ (n + 2) := by
  intro h
  have hle := Int.le_of_dvd (by positivity) h
  have hlt : (2:ℤ) ^ (n + 2) < 2 ^ (n + 3) := by
    apply pow_lt_pow_right₀ (by norm_num)
    omega
  omega

theorem not_dvd_two_add : ¬ (2:ℤ) ^ (n + 3) ∣ (2 + 2 ^ (n + 2)) := by
  intro h
  have h' : (2:ℤ) ^ (n + 2) ∣ 1 + 2 ^ (n + 1) := by
    refine two_pow_dvd_two_mul ?_
    rw [show 2 * (1 + (2:ℤ) ^ (n + 1)) = 2 + 2 ^ (n + 2) by ring]
    exact h
  have h2 : (2:ℤ) ∣ 1 + 2 ^ (n + 1) := dvd_trans (dvd_pow_self 2 (by omega)) h'
  have h3 : (2:ℤ) ∣ (2:ℤ) ^ (n + 1) := dvd_pow_self 2 (by omega)
  obtain ⟨i, hi⟩ := h2
  obtain ⟨j, hj⟩ := h3
  omega








open GenericRecovery in
theorem solution: #(kleinMul n) = 4 := by
  have key : ∀ v w : ℤ, ¬ ((2:ℤ) ^ (n + 3) ∣ v - w) →
      ((v : ℤ) : ZMod (2 ^ (n + 3))) ≠ ((w : ℤ) : ZMod (2 ^ (n + 3))) :=
    fun v w hvw hEq => hvw ((zmod_eq_iff n v w).mp hEq)
  rw [kleinMul, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    refine key _ _ ?_
    rw [show (1 + (2:ℤ) ^ (n + 2)) - (-(1 + 2 ^ (n + 2))) = 2 + 2 ^ (n + 3) by ring]
    intro h
    refine not_dvd_two n ?_
    have h2 : (2:ℤ) ^ (n + 3) ∣ (2 + 2 ^ (n + 3)) - 2 ^ (n + 3) := dvd_sub h dvd_rfl
    simpa using h2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨key _ _ ?_, key _ _ ?_⟩
    · rw [show (-1 : ℤ) - (1 + 2 ^ (n + 2)) = -(2 + 2 ^ (n + 2)) by ring]
      exact fun h => not_dvd_two_add n (dvd_neg.mp h)
    · rw [show (-1 : ℤ) - (-(1 + 2 ^ (n + 2))) = 2 ^ (n + 2) by ring]
      exact not_dvd_two_pow_pred n
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_⟩
    · rw [show (1 : ℤ) - (-1) = 2 by ring]
      exact not_dvd_two n
    · rw [show (1 : ℤ) - (1 + 2 ^ (n + 2)) = -(2 ^ (n + 2)) by ring]
      exact fun h => not_dvd_two_pow_pred n (dvd_neg.mp h)
    · rw [show (1 : ℤ) - (-(1 + 2 ^ (n + 2))) = 2 + 2 ^ (n + 2) by ring]
      exact not_dvd_two_add n
