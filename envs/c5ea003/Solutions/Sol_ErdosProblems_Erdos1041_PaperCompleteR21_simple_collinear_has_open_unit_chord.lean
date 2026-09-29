-- Prove2me | solution 1 for ErdosProblems.Erdos1041.PaperCompleteR21.simple_collinear_has_open_unit_chord
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T12:27:09.523112+00:00
-- url     : https://prove2.me/submissions/fc7dc164-987f-4989-be89-04d1fec88801

import Definitions.Def_ErdosProblems_Erdos1041_PaperCompleteR21_CollinearDiameterWhole
import Theorems.Thm_ErdosProblems_Erdos1041_PaperCompleteR21_sharp_collinear_root_diameter_monic
import Mathlib

/-! A proposed first-use proof importing the public Prove2Me theorem module.
This file has not yet been compiled or submitted. It does not import its own
consumer target. -/

set_option autoImplicit false

open Polynomial Set
open ErdosProblems.Erdos1041.PaperCompleteR21

private theorem native_consumer_exists_pair_diameter {n : ℕ} (hn : 0 < n)
    (base dir : ℂ) (y : Fin n → ℝ) :
    ∃ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
      d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D := by
  classical
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  let g : Fin n × Fin n → ℝ :=
    fun p => dist (base + dir * (y p.1 : ℂ)) (base + dir * (y p.2 : ℂ))
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne g
  refine ⟨g p, ⟨p.1, p.2, rfl⟩, ?_⟩
  rintro d ⟨j, k, rfl⟩
  rw [← hp]
  exact Finset.le_sup' g (Finset.mem_univ (j, k))

theorem solution {n : ℕ} (hn : 2 ≤ n)
    (f : ℂ[X]) (hf : f.IsMonicOfDegree n) (base dir : ℂ)
    (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hindexed : ∀ y : Fin n → ℝ,
      f = (∏ i, (X - C (base + dir * (y i : ℂ)))) →
      Function.Injective (fun i : Fin n => base + dir * (y i : ℂ)))
    (hmargin : ∀ (y : Fin n → ℝ),
      f = (∏ i, (X - C (base + dir * (y i : ℂ)))) →
      ∀ D : ℝ,
        IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) *
          (D / 2) ^ n < 1) :
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ∀ z ∈ segment ℝ a b, ‖f.eval z‖ < 1 := by
  obtain ⟨y, hy, hsharp⟩ :=
    sharp_collinear_root_diameter_monic hn f hf base dir hdir hcol
  obtain ⟨D, hD⟩ := native_consumer_exists_pair_diameter (by omega) base dir y
  obtain ⟨j, k, hjk, _horder, _hadjacent, _hlength, hsegment⟩ := hsharp D hD
  let a : ℂ := base + dir * (y j : ℂ)
  let b : ℂ := base + dir * (y k : ℂ)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro hab
    exact hjk ((hindexed y hy) hab)
  · dsimp [a]
    rw [hy, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  · dsimp [b]
    rw [hy, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  · intro z hz
    exact lt_of_le_of_lt (hsegment z hz) (hmargin y hy D hD)
