-- Prove2me | solution 2 for CompressionOWF.decisionToFinder_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:16:51.268412+00:00
-- url     : https://prove2.me/submissions/dfc31396-ae14-4131-85dd-cf3ee19f0247

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
open CompressionOWF in
theorem solution (D : Str → Str) (dec : Str → Str → ℕ → Bool)
    (fuel : ℕ → ℕ)
    (hdec : ∀ y w n, dec y w n = true ↔ ∃ p : Str, p.length = n ∧ D (w ++ p) = y)
    (y : Str) (hy : Describable D y) (hfuel : K D y ≤ fuel y.length) :
    D (decisionToFinder dec fuel y) = y ∧
      (decisionToFinder dec fuel y).length = K D y := by
  have hleast : ∀ (n : ℕ) (P : ℕ → Bool) (k : ℕ), P k = true → k ≤ n →
      P (leastFrom P n) = true ∧ leastFrom P n ≤ k := by
    intro n
    induction n with
    | zero =>
      intro P k hk hle
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨hk, le_refl _⟩
    | succ n ih =>
      intro P k hk hle
      cases h0 : P 0 with
      | true => simp [leastFrom, h0]
      | false =>
        cases k with
        | zero => rw [h0] at hk; exact absurd hk Bool.false_ne_true
        | succ k' =>
          have := ih (fun j => P (j + 1)) k' hk (by omega)
          simp only [leastFrom, h0, Bool.false_eq_true, if_false]
          exact ⟨this.1, by omega⟩
  have hreb : ∀ (n : ℕ) (w : Str), (∃ p : Str, p.length = n ∧ D (w ++ p) = y) →
      D (rebuild (dec y) n w) = y ∧ (rebuild (dec y) n w).length = w.length + n := by
    intro n
    induction n with
    | zero =>
      rintro w ⟨p, hp, hD⟩
      rw [List.length_eq_zero_iff] at hp
      subst hp
      simp only [List.append_nil] at hD
      exact ⟨hD, by simp [rebuild]⟩
    | succ n ih =>
      rintro w ⟨p, hp, hD⟩
      by_cases hb : dec y (w ++ [false]) n = true
      · have h := ih (w ++ [false]) ((hdec y _ n).mp hb)
        simp only [rebuild]
        rw [if_pos hb]
        refine ⟨h.1, ?_⟩
        rw [h.2]
        simp only [List.length_append, List.length_singleton]
        omega
      · have hex : ∃ p : Str, p.length = n ∧ D ((w ++ [true]) ++ p) = y := by
          match p, hp, hD with
          | [], hp, _ => simp at hp
          | b :: p', hp, hD =>
            cases b with
            | false =>
              exact absurd ((hdec y _ n).mpr ⟨p', by simpa using hp, by simpa using hD⟩) hb
            | true => exact ⟨p', by simpa using hp, by simpa using hD⟩
        have h := ih (w ++ [true]) hex
        simp only [rebuild]
        rw [if_neg hb]
        refine ⟨h.1, ?_⟩
        rw [h.2]
        simp only [List.length_append, List.length_singleton]
        omega
  obtain ⟨p, hpl, hpD⟩ : ∃ p : Str, p.length = K D y ∧ D p = y := by
    obtain ⟨p₀, hp₀⟩ := hy
    exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ D p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
  have hPK : dec y [] (K D y) = true := (hdec y [] _).mpr ⟨p, hpl, by simpa using hpD⟩
  obtain ⟨h1, h2⟩ := hleast (fuel y.length) (fun n => dec y [] n) (K D y) hPK hfuel
  obtain ⟨q, hq, hqD⟩ := (hdec y [] _).mp h1
  have hK : K D y ≤ leastFrom (fun n => dec y [] n) (fuel y.length) := by
    rw [← hq]
    exact Nat.sInf_le ⟨q, rfl, by simpa using hqD⟩
  have hL : leastFrom (fun n => dec y [] n) (fuel y.length) = K D y := le_antisymm h2 hK
  have hfin := hreb (K D y) [] ⟨p, hpl, by simpa using hpD⟩
  show D (rebuild (dec y) (leastFrom (fun n => dec y [] n) (fuel y.length)) []) = y ∧
    (rebuild (dec y) (leastFrom (fun n => dec y [] n) (fuel y.length)) []).length = K D y
  rw [hL]
  simpa using hfin
