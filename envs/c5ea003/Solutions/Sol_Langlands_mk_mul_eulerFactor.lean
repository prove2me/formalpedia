-- Prove2me | solution 1 for Langlands.mk_mul_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:48:00.144875+00:00
-- url     : https://prove2.me/submissions/18d03bb8-ef1a-4e71-bb40-b754f3e93294

-- Sol generated from Shared/LanglandsFunctorialityCore.lean
import Mathlib
import Definitions.Def_Shared_LanglandsFunctorialityCore

/-!
# Langlands functoriality, I: Satake parameters, Hecke eigenvalues and local L-factors

This file develops, over an arbitrary commutative ring, the algebraic skeleton of the
local theory that underlies the Langlands program for `GL(2)`:

* the **Satake parameters** `(a, b)` of an unramified local representation of `GL(2)`;
* the associated **Hecke eigenvalue sequence** `hecke a b k` (the coefficient of the local
  L-function at `p ^ k`), defined by the classical degree-two recursion
  `a_{p^{k+2}} = a_p * a_{p^{k+1}} - χ(p) * a_{p^k}`;
* the **local L-function** as a formal power series, and the fact that it is the inverse of
  the degree-two Euler factor `(1 - a X)(1 - b X)`;
* the **Clebsch–Gordan / Hecke multiplicativity** identity
  `h_{n+d} * h_n = ∑_{i ≤ n} (ab)^{n-i} h_{d + 2i}`,
  which is the Satake-parameter shadow of the decomposition
  `Sym^m ⊗ Sym^n = ⊕_j Sym^{m+n-2j} ⊗ det^j`, and hence the local engine of functoriality;
* the **Ramanujan bound** `‖h_k‖ ≤ k + 1` for tempered (unitary) Satake parameters.

The general power-series lemma `PowerSeriesRecursion.mk_mul_eulerFactor` records the exact
equivalence "linear recursion of Hecke eigenvalues ↔ rationality of the local L-series with
prescribed Euler factor"; it is the workhorse for the `GL(3)` and `GL(4)` transfers in
`LanglandsSymmetricPower.lean`.
-/

open Langlands

open Finset PowerSeries


variable {R : Type*} [CommRing R]

/-- Coefficient of `mk u * (C c * X ^ j)`: a shifted, scaled coefficient of `u`. -/
lemma coeff_mk_mul_CX (u : ℕ → R) (c : R) (j m : ℕ) :
    coeff m (PowerSeries.mk u * (C c * X ^ j)) = if j ≤ m then c * u (m - j) else 0 := by
  rw [show PowerSeries.mk u * (C c * X ^ j) = (C c * PowerSeries.mk u) * X ^ j by ring,
    coeff_mul_X_pow']
  split <;> simp

/-- Coefficient of a monomial `C a * X ^ j`. -/
lemma coeff_CX (a : R) (j m : ℕ) : coeff m (C a * X ^ j) = if m = j then a else 0 := by
  rw [coeff_C_mul, coeff_X_pow]; split <;> simp







variable {R : Type*} [CommRing R]












variable {R : Type*} [CommRing R]














open Langlands in
theorem solution(u : ℕ → R) (e : ℕ → R) (d : ℕ) (B : ℕ → R)
    (hB : ∀ m, B m = ∑ j ∈ range (m + 1), e j * u (m - j))
    (hrec : ∀ k, ∑ j ∈ range (d + 1), e j * u (k + d - j) = 0) :
    PowerSeries.mk u * (∑ j ∈ range (d + 1), C (e j) * X ^ j)
      = ∑ m ∈ range d, C (B m) * X ^ m := by
  ext m
  rw [Finset.mul_sum]
  simp only [map_sum, coeff_mk_mul_CX, coeff_CX]
  by_cases hm : m < d
  · -- low-degree coefficients: both sides are the truncated convolution
    have hR : ∑ m' ∈ range d, (if m = m' then B m' else 0) = B m := by
      rw [Finset.sum_ite_eq (range d) m B, if_pos (Finset.mem_range.mpr hm)]
    have hL : ∑ j ∈ range (d + 1), (if j ≤ m then e j * u (m - j) else 0) = B m := by
      have hcast : ∀ j ∈ range (d + 1), (if j ≤ m then e j * u (m - j) else 0)
          = if j ∈ range (m + 1) then e j * u (m - j) else 0 := by
        intro j _
        simp
      rw [Finset.sum_congr rfl hcast, Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (by
          intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega), hB]
    rw [hL, hR]
  · -- high-degree coefficients: the recursion makes them vanish
    push_neg at hm
    have hzero : ∑ j ∈ range (d + 1), (if j ≤ m then e j * u (m - j) else 0) = 0 := by
      have hshift : ∀ j ∈ range (d + 1), (if j ≤ m then e j * u (m - j) else 0)
          = e j * u ((m - d) + d - j) := by
        intro j hj
        have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hjm : j ≤ m := le_trans hjd hm
        rw [if_pos hjm, Nat.sub_add_cancel hm]
      rw [Finset.sum_congr rfl hshift]
      exact hrec (m - d)
    rw [hzero, Finset.sum_eq_zero]
    intro m' hm'
    have hne : ¬ (m = m') := by
      have := Finset.mem_range.mp hm'
      omega
    simp [hne]
