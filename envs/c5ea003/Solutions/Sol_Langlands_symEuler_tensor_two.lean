-- Prove2me | solution 1 for Langlands.symEuler_tensor_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:49:11.341638+00:00
-- url     : https://prove2.me/submissions/025644b5-f104-4fdd-afda-9daabaaf01b8

-- Sol generated from Shared/LanglandsTensorTransfer.lean
import Mathlib
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






lemma satake_mul_sq_a (m : ℕ) (a b : R) (i : ℕ) :
    a ^ 2 * symSatake m a b i = symSatake (m + 2) a b (i + 2) := by
  rw [symSatake, symSatake, show m + 2 - (i + 2) = m - i by omega]
  ring

lemma satake_mul_sq_b (m : ℕ) (a b : R) (i : ℕ) (hi : i ≤ m) :
    b ^ 2 * symSatake m a b i = symSatake (m + 2) a b i := by
  rw [symSatake, symSatake, show m + 2 - i = (m - i) + 2 by omega, pow_add]
  ring

lemma satake_twist_two (m : ℕ) (a b : R) (j : ℕ) (hj : j < m) :
    (a * b) ^ 2 * symSatake (m - 1) a b j = symSatake (m + 3) a b (j + 2) := by
  rw [symSatake, symSatake, show m + 3 - (j + 2) = (m - 1 - j) + 2 by omega, pow_add, mul_pow]
  ring

/-- Shifting a product by two positions. -/
lemma prod_shift_two (f : ℕ → PowerSeries R) (n : ℕ) :
    (∏ i ∈ range n, f (i + 2)) * (f 1 * f 0) = ∏ i ∈ range (n + 2), f i := by
  rw [Finset.prod_range_succ' f (n + 1), Finset.prod_range_succ' (fun i => f (i + 1)) n]
  ring





variable {R : Type*} [CommRing R]














open Langlands in
theorem solution(m : ℕ) (a b : R) :
    (∏ i ∈ range (m + 2),
        ((1 - C (a ^ 2 * symSatake (m + 1) a b i) * X)
          * (1 - C ((a * b) * symSatake (m + 1) a b i) * X)
          * (1 - C (b ^ 2 * symSatake (m + 1) a b i) * X)))
      = symEuler (m + 3) a b
          * (∏ i ∈ range (m + 2), (1 - C ((a * b) * symSatake (m + 1) a b i) * X))
          * ∏ j ∈ range m, (1 - C ((a * b) ^ 2 * symSatake (m - 1) a b j) * X) := by
  set f : ℕ → PowerSeries R := fun i => 1 - C (symSatake (m + 3) a b i) * X with hf
  set g : ℕ → PowerSeries R := fun i => 1 - C ((a * b) * symSatake (m + 1) a b i) * X with hg
  have hLHS : (∏ i ∈ range (m + 2),
      ((1 - C (a ^ 2 * symSatake (m + 1) a b i) * X)
        * (1 - C ((a * b) * symSatake (m + 1) a b i) * X)
        * (1 - C (b ^ 2 * symSatake (m + 1) a b i) * X)))
      = ∏ i ∈ range (m + 2), (f (i + 2) * g i * f i) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have him : i ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [satake_mul_sq_a (m + 1) a b i, satake_mul_sq_b (m + 1) a b i him]
  have hTwist : (∏ j ∈ range m, (1 - C ((a * b) ^ 2 * symSatake (m - 1) a b j) * X))
      = ∏ j ∈ range m, f (j + 2) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [satake_twist_two m a b j (Finset.mem_range.mp hj)]
  have hSym : symEuler (m + 3) a b = ∏ i ∈ range (m + 4), f i := rfl
  rw [hLHS, hTwist, hSym, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← prod_shift_two f (m + 2), ← prod_shift_two f m]
  ring
