-- Prove2me | solution 2 for CompressionOWF.owf_iff_approx_compression_hard
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T10:01:20.856309+00:00
-- url     : https://prove2.me/submissions/b08894a2-b2f9-434a-a714-69c207a1097c

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
open CompressionOWF in
theorem solution (C : SearchClosedClass) (δ : ℕ → ℕ) :
    (∃ f, OneWayIn C f) ↔
    (∃ D, D ∈ C.Comp ∧ HonestIn C D ∧ ∀ A ∈ C.Comp, ¬ ApproxShortestFinder D A δ) := by
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
  constructor
  · rintro ⟨f, hfC, hfH, hno⟩
    exact ⟨f, hfC, hfH, fun A hA hS => hno A hA (fun y hy => (hS y hy).1)⟩
  · rintro ⟨D, hDC, ⟨b, hb, hbK⟩, hhard⟩
    by_contra hnone
    have hinv : ∀ l, ∃ A ∈ C.Comp, Inverts (guardFun D l) A := by
      intro l
      by_contra hl
      push Not at hl
      apply hnone
      refine ⟨guardFun D l, C.guard_mem D hDC l, ⟨fun n => max l n,
        C.allowed_max _ _ (C.allowed_const l) C.allowed_id, ?_⟩, hl⟩
      rintro y ⟨p, rfl⟩
      have hK : K (guardFun D l) (guardFun D l p) ≤ p.length := Nat.sInf_le ⟨p, rfl, rfl⟩
      show K (guardFun D l) (guardFun D l p) ≤ max l (guardFun D l p).length
      by_cases hp : p.length ≤ l
      · exact hK.trans (le_max_of_le_left hp)
      · have : (guardFun D l p).length = p.length + 1 := by simp [guardFun, hp]
        rw [this]
        exact hK.trans (le_max_of_le_right (Nat.le_succ _))
    choose A hAC hAinv using hinv
    apply hhard (searchFinder D A b) (C.search_mem D hDC A hAC b hb)
    intro y hy
    have h := hSF D A b hAinv y hy (hbK y hy)
    exact ⟨h.1, by rw [h.2]; exact Nat.le_add_right _ _⟩
