-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.mem_trainsR_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:59:30.89823+00:00
-- url     : https://prove2.me/submissions/c09e498a-7a61-470c-a06f-b4412ccf2b40

-- Sol generated from Probability/RefractoryGeneralized.lean
import Mathlib
import Definitions.Def_Probability_RefractoryGeneralized
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Temporal codes with an `r`-bin refractory period

`RefractorySpikeTrains.lean` (in this directory) treats the case of an absolute refractory period of
one time bin: no two spikes in *adjacent* bins, giving the Fibonacci capacity
`fib (T + 2)`.  Real neurons have a refractory period spanning several bins.
This file develops the general case: a spike must be followed by at least `r`
silent bins (a spike in one of the last `r` bins of the window is allowed, the
window simply ends).

## Results

1. `okB` — the admissibility predicate for an `r`-bin refractory period, and
   `trainsR`, an explicit finset of admissible spike trains defined by the
   refractory recursion.
2. `mem_trainsR_iff` — the recursion is correct: `trainsR r n` is *exactly* the
   set of length-`n` binary words in which every spike is followed by `r`
   silent bins (or by the end of the window).
3. `card_trainsR_succ`, `card_trainsR_recursion` — the capacity recursion
   `c_r(n + r + 1) = c_r(n + r) + c_r(n)`, whose characteristic equation is
   `x ^ (r + 1) = x ^ r + 1`.
4. `card_trainsR_one` — for `r = 1` the capacity is `fib (n + 2)`, recovering
   the theorem of `RefractorySpikeTrains.lean` from the general recursion.
5. `card_trainsR_two_succ3` — for `r = 2` the capacity obeys
   `c(n + 3) = c(n + 2) + c(n)` (Narayana's cows, OEIS A000930).
6. `trainsR_antitone`, `card_trainsR_antitone` — a longer refractory period can
   only lose capacity.
7. `card_trainsR_le_pow`, `temporal_rate_le_general` — a general rate bound:
   over a window of `(r + 1) * m` bins the capacity is at most `(2 ^ r + 1) ^ m`.
8. `card_trainsR_two_le_pow`, `temporal_rate_two_le` — the sharper `r = 2` bound
   `c(3m) ≤ 4 ^ m`, i.e. at most `2/3` of a bit per time bin (against `4/5` for
   `r = 1` and `1` for the unconstrained channel): refractoriness strictly
   decreases the information rate.
9. `card_trainsR_ge` — a matching lower bound `n + 1 ≤ c_r(n)`, so the capacity
   is never trivial.
-/

open Catalog.Probability.NeuralCoding.Temporal

open Finset




theorem okB_true_cons (r : ℕ) (l : List Bool) :
    okB r (true :: l) = ((l.take r).all (fun b => !b) && okB r l) := rfl

@[simp] theorem okB_nil (r : ℕ) : okB r [] = true := rfl

@[simp] theorem okB_false_cons (r : ℕ) (l : List Bool) :
    okB r (false :: l) = okB r l := rfl

/-- Prefixing silent bins does not affect admissibility. -/
theorem okB_replicate_false_append (r k : ℕ) (l : List Bool) :
    okB r (List.replicate k false ++ l) = okB r l := by
  induction k with
  | zero => simp
  | succ k ih => simpa [List.replicate_succ] using ih

@[simp] theorem okB_replicate_false (r k : ℕ) : okB r (List.replicate k false) = true := by
  have := okB_replicate_false_append r k []
  simpa using this


theorem trainsR_zero (r : ℕ) : trainsR r 0 = {[]} := by rw [trainsR]

theorem trainsR_succ (r n : ℕ) :
    trainsR r (n + 1) =
      (trainsR r n).image (fun l => false :: l) ∪
        (if r ≤ n then
            (trainsR r (n - r)).image (fun l => true :: (List.replicate r false ++ l))
          else {true :: List.replicate n false}) := by rw [trainsR]






























open Catalog.Probability.NeuralCoding.Temporal in
theorem solution(r : ℕ) : ∀ (n : ℕ) (l : List Bool),
    l ∈ trainsR r n ↔ l.length = n ∧ okB r l = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        intro l
        constructor
        · intro h
          rw [trainsR_zero, Finset.mem_singleton] at h
          subst h; simp
        · rintro ⟨hlen, -⟩
          have : l = [] := List.eq_nil_of_length_eq_zero hlen
          simp [trainsR_zero, this]
    | (n + 1) =>
        intro l
        rw [trainsR_succ]
        constructor
        · intro h
          simp only [Finset.mem_union, Finset.mem_image] at h
          rcases h with ⟨m, hm, rfl⟩ | h
          · obtain ⟨hlen, hok⟩ := (ih n (by omega) m).mp hm
            exact ⟨by simp [hlen], by simpa using hok⟩
          · by_cases hr : r ≤ n
            · rw [if_pos hr] at h
              simp only [Finset.mem_image] at h
              obtain ⟨m, hm, rfl⟩ := h
              obtain ⟨hlen, hok⟩ := (ih (n - r) (by omega) m).mp hm
              refine ⟨by simp [hlen]; omega, ?_⟩
              rw [okB_true_cons]
              have htake : (List.replicate r false ++ m).take r = List.replicate r false := by
                simp
              rw [htake, okB_replicate_false_append]
              simp [hok]
            · rw [if_neg hr, Finset.mem_singleton] at h
              subst h
              refine ⟨by simp, ?_⟩
              rw [okB_true_cons]
              simp
        · rintro ⟨hlen, hok⟩
          match l with
          | [] => simp at hlen
          | (false :: m) =>
              refine Finset.mem_union_left _ ?_
              simp only [Finset.mem_image]
              refine ⟨m, (ih n (by omega) m).mpr ⟨by simpa using hlen, by simpa using hok⟩, rfl⟩
          | (true :: m) =>
              have hmlen : m.length = n := by simpa using hlen
              rw [okB_true_cons, Bool.and_eq_true] at hok
              obtain ⟨htake, hokm⟩ := hok
              refine Finset.mem_union_right _ ?_
              have htake' : m.take r = List.replicate (min r n) false := by
                rw [List.eq_replicate_iff]
                constructor
                · simp [hmlen]
                · intro b hb
                  have := List.all_eq_true.mp htake b hb
                  simpa using this
              by_cases hr : r ≤ n
              · rw [if_pos hr]
                simp only [Finset.mem_image]
                refine ⟨m.drop r, ?_, ?_⟩
                · refine (ih (n - r) (by omega) (m.drop r)).mpr ⟨by simp [hmlen], ?_⟩
                  have : okB r m = okB r (m.take r ++ m.drop r) := by
                    rw [List.take_append_drop]
                  rw [this, htake', min_eq_left hr, okB_replicate_false_append] at hokm
                  exact hokm
                · have : List.replicate r false ++ m.drop r = m := by
                    conv_rhs => rw [← List.take_append_drop r m]
                    rw [htake', min_eq_left hr]
                  rw [this]
              · rw [if_neg hr, Finset.mem_singleton]
                have hm : m = List.replicate n false := by
                  have hmt : m.take r = m := List.take_of_length_le (by omega)
                  rw [hmt, min_eq_right (by omega)] at htake'
                  exact htake'
                rw [hm]
