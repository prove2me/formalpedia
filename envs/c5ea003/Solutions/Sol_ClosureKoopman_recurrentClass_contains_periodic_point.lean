-- Prove2me | solution 1 for ClosureKoopman.recurrentClass_contains_periodic_point
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:16:49.325716+00:00
-- url     : https://prove2.me/submissions/8ce691c3-aa90-44b1-97e2-745867d88cea

-- Sol generated from Bridges/ClosureKoopmanReconstruction.lean
import Mathlib
import Definitions.Def_Bridges_ClosureKoopmanReconstruction
/-
# Algebraic–EML Phase-Space Reconstruction via Closure Bialgebras and Koopman Spectra

This file formalizes a bridge between algebraic closure semantics, finite Koopman
spectral theory, character-based phase-space reconstruction, and certified
quantitative bounds with applications to quantum, cryptographic, and ML semantics.

## Central Reconstruction Principle
> Closure-fixed observable algebra + Koopman intertwining + observable separation
> ⇒ reconstructible recurrent phase portrait with explicit stabilization bounds.

Bridge: algebraic closure theory ↔ dynamical systems ↔ quantum semantics ↔
cryptographic stabilization ↔ certified ML robustness.
-/


open Finset Function

open ClosureKoopman

/-! ## Section 1: Closure Orbit Primitives -/












/-! ## Section 2: Closure Observable Structure -/





/-! ## Section 3: Koopman Map and Endomorphism -/










/-! ## Section 4: Evaluation Characters -/




/-! ## Section 5: Observable Separation and Phase-Space Reconstruction -/







/-! ## Section 6: Finite Dynamics and Recurrence -/


open Classical








/-! ## Section 7: Quantitative Bounds -/















open ClosureKoopman in
theorem solution    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : σ → σ) (s : σ) :
    ∃ t ∈ recurrentClass f s, ∃ n : ℕ, 0 < n ∧ (f^[n]) t = t := by
  set N := Fintype.card σ
  -- By pigeonhole: among f^N(s), ..., f^{2N}(s), two must coincide
  have hpig : ∃ (i j : Fin (N + 1)), i < j ∧
      (f^[N + i.val]) s = (f^[N + j.val]) s := by
    by_contra hall
    push_neg at hall
    have hinj : Function.Injective
        (fun i : Fin (N + 1) => (f^[N + i.val]) s) := by
      intro a b hab
      rcases lt_trichotomy a b with h | h | h
      · exact absurd hab (hall a b h)
      · exact h
      · exact absurd hab.symm (hall b a h)
    have hle := Fintype.card_le_of_injective _ hinj
    simp [N] at hle
  obtain ⟨i, j, hij, heq⟩ := hpig
  set t := (f^[N + i.val]) s
  refine ⟨t, ?_, j.val - i.val, by omega, ?_⟩
  · simp only [recurrentClass, mem_filter, mem_univ, true_and]
    exact ⟨N + i.val, Nat.le_add_right N i.val, rfl⟩
  · calc (f^[j.val - i.val]) t
        = (f^[j.val - i.val + (N + i.val)]) s := by
          rw [Function.iterate_add_apply]
      _ = (f^[N + j.val]) s := by congr 1; omega
      _ = t := heq.symm
