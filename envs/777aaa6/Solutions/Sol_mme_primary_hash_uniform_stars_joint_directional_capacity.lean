-- Prove2me | solution 1 for mme_primary_hash_uniform_stars_joint_directional_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:32:14.812969+00:00
-- url     : https://prove2.me/submissions/2f72a435-64c1-4cd9-98e8-69d367b01f32

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

private theorem joint_choose_identity (N L G : ℕ) (hLG : L + G = N) :
    (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2 := by
  have hfirst := Nat.choose_mul (n := 2 * N - L) (k := 2 * G) (s := G)
    (by omega)
  have hsymm : Nat.choose (2 * N - L) (2 * G) =
      Nat.choose (2 * N - L) L :=
    Nat.choose_symm_of_eq_add (by omega)
  have hsub : 2 * N - L - G = N := by omega
  have hGsub : 2 * G - G = G := by omega
  rw [hsymm, hsub, hGsub] at hfirst
  have hsecond := Nat.choose_mul (n := 2 * N) (k := N) (s := L) (by omega)
  have hNL : N - L = G := by omega
  have hlast : Nat.choose N L = Nat.choose N G :=
    Nat.choose_symm_of_eq_add hLG.symm
  rw [hNL, hlast] at hsecond
  calc
    _ = Nat.choose (2 * N) L *
        (Nat.choose (2 * N - L) L * Nat.choose (2 * G) G) := by ring
    _ = Nat.choose (2 * N) L *
        (Nat.choose (2 * N - L) G * Nat.choose N G) := by rw [hfirst]
    _ = (Nat.choose (2 * N) L * Nat.choose (2 * N - L) G) *
        Nat.choose N G := by ring
    _ = (Nat.choose (2 * N) N * Nat.choose N G) * Nat.choose N G := by
      rw [← hsecond]
    _ = _ := by ring

/-- The actual uniform-star inequalities jointly preserve the two unshared
directional capacities, while retaining the shared-direction bound separately. -/
theorem solution
    (N L G A H : ℕ) (hLG : L + G = N) (C : ℝ)
    (hA : ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ))
    (hH : (Nat.choose (2 * G) G : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      4 * (Nat.choose N G : ℝ) ^ 2 * (H : ℝ)) :
    ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2) ∧
    (((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ)) ∧
    ((Nat.choose (2 * N) N : ℝ) *
      Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      4 * (A : ℝ) * (H : ℝ)) := by
  have hid := joint_choose_identity N L G hLG
  refine ⟨hid, hA, ?_⟩
  have hX : 0 < (Nat.choose N G : ℝ) ^ 2 := by
    have : 0 < Nat.choose N G := Nat.choose_pos (by omega)
    positivity
  have hexp : Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) =
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) *
        Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod := mul_le_mul hA hH (by positivity) (by positivity)
  apply (mul_le_mul_iff_right₀ hX).mp
  calc
    _ = (((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
          Nat.choose (2 * G) G : ℕ) : ℝ) *
        Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
      rw [hid]
      push_cast
      ring
    _ = ((((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
        Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ))) *
        ((Nat.choose (2 * G) G : ℝ) *
          Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)))) := by
      rw [hexp]
      push_cast
      ring
    _ ≤ (A : ℝ) * (4 * (Nat.choose N G : ℝ) ^ 2 * (H : ℝ)) := hprod
    _ = _ := by ring
