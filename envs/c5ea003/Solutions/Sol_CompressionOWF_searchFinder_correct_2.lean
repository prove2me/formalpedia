-- Prove2me | solution 2 for CompressionOWF.searchFinder_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:10:42.639463+00:00
-- url     : https://prove2.me/submissions/a4ec59ab-30b6-459b-abeb-52884d7c1d2e

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution (f : Str → Str) (A : ℕ → Str → Str) (fuel : ℕ → ℕ)
    (hA : ∀ l, Inverts (guardFun f l) (A l)) (y : Str) (hy : Describable f y)
    (hfuel : K f y ≤ fuel y.length) :
    f (searchFinder f A fuel y) = y ∧ (searchFinder f A fuel y).length = K f y := by
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
  have hshort : ∀ (f : Str → Str) (y : Str), Describable f y →
      ∃ p : Str, p.length = K f y ∧ f p = y := by
    intro f y hy
    obtain ⟨p₀, hp₀⟩ := hy
    exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ f p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
  have hSF : ∀ (f : Str → Str) (A : ℕ → Str → Str) (fuel : ℕ → ℕ),
      (∀ l, Inverts (guardFun f l) (A l)) → ∀ (y : Str), Describable f y →
      K f y ≤ fuel y.length →
      f (searchFinder f A fuel y) = y ∧ (searchFinder f A fuel y).length = K f y := by
    intro f A fuel hA y hy hfuel
    obtain ⟨p, hpl, hpf⟩ := hshort f y hy
    unfold searchFinder
    generalize hP : (fun l => decide (guardFun f l (A l (true :: y)) = true :: y)) = P
    have hPK : P (K f y) = true := by
      rw [← hP]
      simp only [decide_eq_true_eq]
      exact hA (K f y) (true :: y) ⟨p, by simp [guardFun, hpl, hpf]⟩
    have hgood : ∀ l, P l = true → f (A l (true :: y)) = y ∧ (A l (true :: y)).length ≤ l := by
      intro l hl
      rw [← hP] at hl
      simp only [decide_eq_true_eq, guardFun] at hl
      split_ifs at hl with hlen
      · simp only [List.cons.injEq, true_and] at hl
        exact ⟨hl, hlen⟩
      · simp at hl
    obtain ⟨h1, h2⟩ := hleast (fuel y.length) P (K f y) hPK hfuel
    obtain ⟨hf, hlen⟩ := hgood _ h1
    have hK : K f y ≤ (A (leastFrom P (fuel y.length)) (true :: y)).length :=
      Nat.sInf_le ⟨_, rfl, hf⟩
    exact ⟨hf, by omega⟩
  exact hSF f A fuel hA y hy hfuel
