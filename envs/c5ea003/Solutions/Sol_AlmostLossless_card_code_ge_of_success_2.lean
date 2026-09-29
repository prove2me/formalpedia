-- Prove2me | solution 2 for AlmostLossless.card_code_ge_of_success
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T12:17:59.283414+00:00
-- url     : https://prove2.me/submissions/e53426cc-380a-4a81-a1ab-53798460205c

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy
open AlmostLossless NonArchInfoTheory in
theorem solution {α : Type*} [Fintype α] {Code : Type*} [DecidableEq α] [Nonempty α] [Fintype Code]
    (μ : FinProbDist α) (sch : Scheme α Code) (ε : ℝ) (h : 1 - ε ≤ successProb μ sch) :
    (1 - ε) / maxMass μ ≤ (Fintype.card Code : ℝ) := by
  have hle : ∀ x, μ.mass x ≤ maxMass μ := fun x =>
    Finset.le_sup' μ.mass (Finset.mem_univ x)
  have hpos : 0 < maxMass μ := by
    have h1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * maxMass μ := by
      rw [← μ.mass_sum_one]
      calc ∑ x, μ.mass x ≤ ∑ _x : α, maxMass μ := Finset.sum_le_sum (fun x _ => hle x)
        _ = (Fintype.card α : ℝ) * maxMass μ := by simp
    by_contra hneg
    push Not at hneg
    have : (Fintype.card α : ℝ) * maxMass μ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg
    linarith
  have hsucc : successProb μ sch ≤ ((successSet sch).card : ℝ) * maxMass μ := by
    unfold successProb setMass
    calc ∑ x ∈ successSet sch, μ.mass x ≤ ∑ _x ∈ successSet sch, maxMass μ :=
          Finset.sum_le_sum (fun x _ => hle x)
      _ = ((successSet sch).card : ℝ) * maxMass μ := by simp
  have hcard : (successSet sch).card ≤ Fintype.card Code := by
    have hinj : Set.InjOn sch.enc (successSet sch) := by
      intro x hx y hy hxy
      simp only [successSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
      have : some x = some y := by rw [← hx, ← hy, hxy]
      exact Option.some.inj this
    have := Finset.card_le_card_of_injOn sch.enc (fun x _ => Finset.mem_univ (sch.enc x)) hinj
    simpa using this
  rw [div_le_iff₀ hpos]
  have hc : ((successSet sch).card : ℝ) ≤ (Fintype.card Code : ℝ) := by exact_mod_cast hcard
  nlinarith [hpos.le]
