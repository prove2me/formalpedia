-- Prove2me | solution 1 for Langlands.coeff_L1_mul_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:18:58.690013+00:00
-- url     : https://prove2.me/submissions/71349626-66d0-4ca0-aa7d-11cd1df7fcb3

-- Sol generated from Shared/LanglandsTensorTransfer.lean
import Mathlib
import Definitions.Def_Shared_LanglandsFunctorialityCore
import Definitions.Def_Shared_LanglandsSymmetricPower

/-!
# Langlands functoriality, III: tensor transfer and Ramanujan bounds for the lifts

This file proves two families of results that go beyond the individual liftings of
`Shared.LanglandsSymmetricPower`.

## Tensor (Rankin–Selberg) functoriality in arbitrary symmetric power degree

`symEuler_tensor_one` and `symL_tensor_one` prove, for **every** `m`, the local
Rankin–Selberg factorisation

`L(Sym^m π × π, X) = L(Sym^{m+1} π, X) · L(Sym^{m-1} π ⊗ χ, X)`,

i.e. the functorial decomposition `Sym^m ⊗ Sym^1 = Sym^{m+1} ⊕ (Sym^{m-1} ⊗ det)` realised
on Satake parameters, Euler factors and Dirichlet coefficients.  The `m = 1` case is the
Gelbart–Jacquet identity `L(π × π) = L(Sym^2 π) L(χ)` already visible in
`rankin_selberg_sym_two`.

## Ramanujan bounds transported along functoriality

`hecke3_eq_prod` identifies the abstract `GL(3)` Hecke eigenvalues with the complete
homogeneous symmetric functions of the three Satake parameters, and `symL_two_coeff_norm_le`
deduces the full Ramanujan bound `|b_{p^k}| ≤ (k+1)(k+2)/2` for **all** powers of `p` for the
Gelbart–Jacquet lift of a tempered representation — not merely for `k = 1`.
-/

open Langlands

open Finset PowerSeries


variable {R : Type*} [CommRing R]














variable {R : Type*} [CommRing R]














open Langlands in
lemma solution(x : ℂ) (hx : ‖x‖ = 1) (G : PowerSeries ℂ) (B : ℕ → ℝ)
    (hB : ∀ j, ‖coeff j G‖ ≤ B j) (k : ℕ) :
    ‖coeff k (L1 x * G)‖ ≤ ∑ j ∈ range (k + 1), B j := by
  rw [coeff_mul]
  have step : ∀ ij ∈ Finset.antidiagonal k,
      ‖coeff ij.1 (L1 x) * coeff ij.2 G‖ ≤ B ij.2 := by
    intro ij _
    rw [norm_mul]
    have : ‖coeff ij.1 (L1 x)‖ = 1 := by
      rw [L1]
      simp [norm_pow, hx]
    rw [this, one_mul]
    exact hB ij.2
  calc ‖∑ ij ∈ Finset.antidiagonal k, coeff ij.1 (L1 x) * coeff ij.2 G‖
      ≤ ∑ ij ∈ Finset.antidiagonal k, ‖coeff ij.1 (L1 x) * coeff ij.2 G‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ Finset.antidiagonal k, B ij.2 := Finset.sum_le_sum step
    _ = ∑ i ∈ range (k + 1), B (k - i) := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun _ j => B j)]
    _ = ∑ j ∈ range (k + 1), B j := by
        rw [← Finset.sum_range_reflect (fun j => B j) (k + 1)]
        refine Finset.sum_congr rfl ?_
        intro i hi
        have := Finset.mem_range.mp hi
        congr 1
