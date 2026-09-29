-- Prove2me | solution 2 for Hashimoto.trace_hashimoto_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T22:10:33.106843+00:00
-- url     : https://prove2.me/submissions/d0020c25-3298-4de0-a62d-7b2a3e4ee6a6

import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
open Finset RelWalkCount SimpleGraph Hashimoto in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) : (hashimoto G ^ n).trace = (closedNBWalks G n).card := by
  -- entries of `Bⁿ` count non-backtracking walks
  have hpow : ∀ (n : ℕ) (a b : G.Dart),
      (relMatrix (NBAdj G) ^ n) a b = (walks (NBAdj G) n a b).card := by
    -- every walk starts at its source
    have hhead : ∀ (n : ℕ) (a b : G.Dart) (l : List G.Dart), l ∈ walks (NBAdj G) n a b → l.head? = some a := by
      intro n a b l hl
      cases n with
      | zero =>
        simp only [walks] at hl
        split_ifs at hl with hab
        · rw [Finset.mem_singleton] at hl
          rw [hl]
          rfl
        · simp at hl
      | succ n =>
        simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
        obtain ⟨c, -, l', -, rfl⟩ := hl
        rfl
    intro n
    induction n with
    | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      simp only [walks]
      split_ifs <;> simp
    | succ n ih =>
      intro a b
      rw [pow_succ', Matrix.mul_apply]
      simp only [walks]
      -- the images for different second vertices are disjoint
      rw [Finset.card_biUnion]
      · rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ih c b, Finset.card_image_of_injective _ (List.cons_injective)]
        simp only [relMatrix, Matrix.of_apply]
        split_ifs <;> simp
      · intro c _ c' _ hcc'
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro l hl hl'
        rw [Finset.mem_image] at hl hl'
        obtain ⟨l₁, h₁, rfl⟩ := hl
        obtain ⟨l₂, h₂, heq⟩ := hl'
        have h12 : l₂ = l₁ := List.cons_injective heq
        subst h12
        have e1 := hhead n c b _ h₁
        have e2 := hhead n c' b _ h₂
        rw [e1] at e2
        exact hcc' (Option.some_injective _ e2)
  -- every walk starts at its source
  have hhead : ∀ (n : ℕ) (a b : G.Dart) (l : List G.Dart), l ∈ walks (NBAdj G) n a b → l.head? = some a := by
    intro n a b l hl
    cases n with
    | zero =>
      simp only [walks] at hl
      split_ifs at hl with hab
      · rw [Finset.mem_singleton] at hl
        rw [hl]
        rfl
      · simp at hl
    | succ n =>
      simp only [walks, Finset.mem_biUnion, Finset.mem_image] at hl
      obtain ⟨c, -, l', -, rfl⟩ := hl
      rfl
  -- the trace counts rooted closed walks (different roots give different walks)
  unfold hashimoto closedNBWalks closedWalks
  rw [Matrix.trace, Finset.card_biUnion]
  · simp only [Matrix.diag, hpow]
  · intro a _ b _ hab
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro l ha hb
    have h1 := hhead n a a l ha
    have h2 := hhead n b b l hb
    rw [h1] at h2
    exact hab (Option.some_injective _ h2)
