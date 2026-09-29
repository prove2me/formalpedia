-- Prove2me | solution 2 for Hashimoto.Examples.C5_closedNBWalks
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:05:46.727315+00:00
-- url     : https://prove2.me/submissions/4f799845-3e59-445e-8249-6bfdee98623a

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_Examples
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
open Hashimoto Hashimoto.Examples RelWalkCount in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (closedNBWalks C5 n).card = if 5 ∣ n then 10 else 0 := by
  classical
  -- the non-backtracking successor on the pentagon, as a map on vertex pairs
  -- `σ (u, v) = (v, 2v - u)`: a dart has exactly one non-backtracking successor
  have hsucc : ∀ d d' : C5.Dart,
      NBAdj C5 d d' ↔ d'.toProd = (d.toProd.2, 2 * d.toProd.2 - d.toProd.1) := by decide
  have hex : ∀ d : C5.Dart, ∃ c : C5.Dart, c.toProd = (d.toProd.2, 2 * d.toProd.2 - d.toProd.1) := by
    decide
  have hper : ∀ d : C5.Dart,
      (fun p : Fin 5 × Fin 5 => (p.2, 2 * p.2 - p.1))^[5] d.toProd = d.toProd := by decide
  have hnoper : ∀ d : C5.Dart, ∀ k : Fin 4,
      (fun p : Fin 5 × Fin 5 => (p.2, 2 * p.2 - p.1))^[k.val + 1] d.toProd ≠ d.toProd := by decide
  have hcard : Fintype.card C5.Dart = 10 := by decide
  set σ : Fin 5 × Fin 5 → Fin 5 × Fin 5 := fun p => (p.2, 2 * p.2 - p.1) with hσ
  -- walks from `a` to `b` of length `m`: one if `σᵐ a = b`, none otherwise
  have hwalks : ∀ (m : ℕ) (a b : C5.Dart),
      (walks (NBAdj C5) m a b).card = if σ^[m] a.toProd = b.toProd then 1 else 0 := by
    intro m
    induction m with
    | zero =>
      intro a b
      simp only [walks, Function.iterate_zero, id]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos (congrArg _ hab), Finset.card_singleton]
      · rw [if_neg hab, if_neg (fun h => hab (SimpleGraph.Dart.ext _ _ h)), Finset.card_empty]
    | succ m ih =>
      intro a b
      obtain ⟨c, hc⟩ := hex a
      have hfilter : (Finset.univ.filter fun c' => NBAdj C5 a c') = {c} := by
        ext c'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [hsucc]
        constructor
        · intro h
          exact SimpleGraph.Dart.ext _ _ (h.trans hc.symm)
        · rintro rfl
          exact hc
      simp only [walks]
      rw [hfilter, Finset.singleton_biUnion,
        Finset.card_image_of_injective _ List.cons_injective, ih c,
        Function.iterate_succ_apply, hc]
  -- every walk starts at its source, so walks with different roots are different
  have hhead : ∀ (m : ℕ) (a b : C5.Dart) (l : List C5.Dart),
      l ∈ walks (NBAdj C5) m a b → l.head? = some a := by
    intro m a b l hl
    cases m with
    | zero =>
      simp only [walks] at hl
      split_ifs at hl with hab
      · rw [Finset.mem_singleton] at hl
        rw [hl]
        rfl
      · simp at hl
    | succ m =>
      simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
      obtain ⟨c, -, l', -, rfl⟩ := hl
      rfl
  have hsum : (closedNBWalks C5 n).card
      = ∑ a : C5.Dart, (if σ^[n] a.toProd = a.toProd then 1 else 0) := by
    unfold closedNBWalks closedWalks
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun a _ => hwalks n a a
    · intro a _ b _ hab
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro l ha hb
      have h1 := hhead n a a l ha
      have h2 := hhead n b b l hb
      rw [h1] at h2
      exact hab (Option.some_injective _ h2)
  -- `σ` has period exactly `5` on every dart
  have hmult : ∀ (d : C5.Dart) (q : ℕ), σ^[5 * q] d.toProd = d.toProd := by
    intro d q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [show 5 * (q + 1) = 5 + 5 * q by ring, Function.iterate_add_apply, ih]
      exact hper d
  have hiter : ∀ d : C5.Dart, σ^[n] d.toProd = σ^[n % 5] d.toProd := by
    intro d
    conv_lhs => rw [← Nat.mod_add_div n 5, Function.iterate_add_apply, hmult d (n / 5)]
  rw [hsum]
  split_ifs with h5
  · have hall : ∀ a : C5.Dart, σ^[n] a.toProd = a.toProd := by
      intro a
      rw [hiter a, Nat.mod_eq_zero_of_dvd h5]
      rfl
    simp only [hall, if_true, Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul, mul_one]
  · have hnone : ∀ a : C5.Dart, σ^[n] a.toProd ≠ a.toProd := by
      intro a
      rw [hiter a]
      have hr : n % 5 ≠ 0 := fun h => h5 (Nat.dvd_of_mod_eq_zero h)
      have := hnoper a ⟨n % 5 - 1, by omega⟩
      simp only at this
      rwa [show n % 5 - 1 + 1 = n % 5 by omega] at this
    simp only [hnone, if_false, Finset.sum_const_zero]
