-- Prove2me | solution 1 for DeltaPetrie.petrieBlock_dvd_X_pow_sub_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:10:02.701681+00:00
-- url     : https://prove2.me/submissions/cf40f4b6-2e39-44ed-b214-e9e4826572b1

import Mathlib
import Definitions.Def_Novelty_DeltaPetrieSchurPositivity
open Polynomial DeltaPetrie in
theorem solution {k n : ℕ} (hk : 2 ≤ k) :
    petrieBlock k ∣ (X ^ n - 1 : ℂ[X]) ↔ k ∣ n := by
  -- `𝔭_k · (X − 1) = X^k − 1`
  have hgeom : petrieBlock k * (X - 1) = X ^ k - 1 := by
    unfold petrieBlock
    exact geom_sum_mul X k
  constructor
  · -- a primitive `k`-th root of unity `ζ ≠ 1` is a root of `𝔭_k`, hence `ζ^n = 1`
    intro h
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ k :=
      ⟨_, Complex.isPrimitiveRoot_exp k (by omega)⟩
    have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
    have hroot : (petrieBlock k).eval ζ = 0 := by
      have := congrArg (eval ζ) hgeom
      simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_one, hζ.pow_eq_one, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hζ1)
    obtain ⟨q, hq⟩ := h
    have := congrArg (eval ζ) hq
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, hroot, zero_mul] at this
    exact hζ.dvd_of_pow_eq_one n (sub_eq_zero.mp this)
  · -- `𝔭_k ∣ X^k − 1 ∣ X^(k m) − 1`
    rintro ⟨m, rfl⟩
    have h1 : petrieBlock k ∣ X ^ k - 1 := ⟨X - 1, hgeom.symm⟩
    refine h1.trans ?_
    have := sub_dvd_pow_sub_pow (X ^ k : ℂ[X]) 1 m
    rwa [one_pow, ← pow_mul] at this
