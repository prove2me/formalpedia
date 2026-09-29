-- Prove2me | solution 1 for ChebotarevGeodesic.chebotarev_exponent_can_be_strictly_worse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:44:08.024609+00:00
-- url     : https://prove2.me/submissions/24bb997e-1ba9-4fce-8b48-fef735e3b7c9

-- Sol generated from Shared/ChebotarevGeodesicQuotientExponent.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_self
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_growth
import Theorems.Thm_ChebotarevGeodesic_sum_classDensity
/-
# Exponents under quotients: the pushforward can only improve them

Continuation of `Shared.ChebotarevGeodesicQuotient` (which proves `chebotarev_pushforward`:
the Chebotarev estimate descends to every quotient with the *same* exponent) and
`Shared.ChebotarevGeodesicTransfer` (which introduces `jointExponentSet` and
`jointOptimalExponent`).  This file addresses conjecture C1 of `FUTURE_DIRECTIONS.md`.

* `jointExponentSet_subset_pushforward` : every exponent admissible for the family of class
  counting functions of `G` is admissible for the pushed-forward family of a quotient `H`;
* `jointOptimalExponent_pushforward_le` : hence the joint optimal exponent can only *drop*
  along a surjection `G ↠ H`;
* `chebotarev_exponent_can_be_strictly_worse` : and the drop can be strict, in the extreme
  possible way.  For any finite group with at least two conjugacy classes there are class
  counting functions whose *total* is exactly the main term `li` — so the pushforward to the
  trivial quotient (that is, the prime geodesic theorem) holds with **every** exponent —
  while no single class satisfies **any** exponent below `β`.  The mechanism is cancellation
  inside a fibre: the deviations `w C · x^β` sum to zero.

Consequently the inequality of `jointOptimalExponent_pushforward_le` is genuinely one-sided:
knowing the prime geodesic theorem with a good exponent says nothing about the individual
Chebotarev estimates, whereas the converse implication is the content of
`chebotarev_pushforward`.
-/


open Finset Filter Function
open scoped Topology

open ChebotarevGeodesic


variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Group H] [Fintype H] [DecidableEq H]
  [Fintype (ConjClasses G)] [Fintype (ConjClasses H)]




/-! ## Strictness: total cancellation inside a fibre -/



open ChebotarevGeodesic in
theorem solution(G : Type*) [Group G] [Fintype G]
    [DecidableEq G] [Fintype (ConjClasses G)]
    (hcard : 2 ≤ Fintype.card (ConjClasses G)) (li : ℝ → ℝ) {θ β : ℝ} (hθβ : θ < β) :
    ∃ piC : ConjClasses G → ℝ → ℝ,
      (∀ x, ∑ C : ConjClasses G, piC C x = li x) ∧
      (∀ θ' : ℝ, HasErrorExponent (fun x => ∑ C : ConjClasses G, piC C x) li θ') ∧
      (∀ C, ¬ HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) := by
  classical
  set n : ℕ := Fintype.card (ConjClasses G) with hndef
  have hne : Nonempty (ConjClasses G) := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨C₀⟩ := hne
  -- deviations summing to zero, each of absolute value at least one
  set w : ConjClasses G → ℝ := fun C => (if C = C₀ then (n : ℝ) else 0) - 1 with hwdef
  have hwsum : ∑ C : ConjClasses G, w C = 0 := by
    have h1 : ∑ C : ConjClasses G, (if C = C₀ then (n : ℝ) else 0) = (n : ℝ) := by
      rw [Finset.sum_ite_eq' Finset.univ C₀ (fun _ => (n : ℝ))]
      simp
    have h2 : ∑ _C : ConjClasses G, (1 : ℝ) = (n : ℝ) := by
      simp [hndef]
    simp only [hwdef]
    rw [Finset.sum_sub_distrib, h1, h2, sub_self]
  have hwabs : ∀ C, (1 : ℝ) ≤ |w C| := by
    intro C
    by_cases hC : C = C₀
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
      have hwC : w C = (n : ℝ) - 1 := by simp [hwdef, hC]
      rw [hwC, abs_of_nonneg (by linarith)]
      linarith
    · have hwC : w C = -1 := by simp [hwdef, hC]
      rw [hwC]
      norm_num
  refine ⟨fun C x => classDensity G C * li x + w C * x ^ β, ?_, ?_, ?_⟩
  · intro x
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_classDensity G, one_mul,
      ← Finset.sum_mul, hwsum, zero_mul, add_zero]
  · intro θ'
    have e : (fun x => ∑ C : ConjClasses G, (classDensity G C * li x + w C * x ^ β)) = li := by
      funext x
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_classDensity G, one_mul,
        ← Finset.sum_mul, hwsum, zero_mul, add_zero]
    rw [e]
    exact hasErrorExponent_self li θ'
  · intro C
    refine not_hasErrorExponent_of_growth (c := 1) (β := β) one_pos hθβ fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hxβ : (0 : ℝ) < x ^ β := Real.rpow_pos_of_pos hx0 β
    have hsimp : classDensity G C * li x + w C * x ^ β - classDensity G C * li x
        = w C * x ^ β := by ring
    rw [hsimp, abs_mul, abs_of_pos hxβ]
    exact mul_le_mul_of_nonneg_right (hwabs C) hxβ.le
