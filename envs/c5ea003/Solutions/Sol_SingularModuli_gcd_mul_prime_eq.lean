-- Prove2me | solution 1 for SingularModuli.gcd_mul_prime_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:39.607603+00:00
-- url     : https://prove2.me/submissions/a9824e6b-11ba-40c0-8439-7f7685f4eda5

-- Sol generated from Geometry/SingularModuliCore.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliCore
/-
# Singular Moduli Factoring — Core Counting Layer

This file formalises the *arithmetic core* of the "singular moduli factoring"
method.  Given a semiprime `N = p * q` and an integer polynomial `f` (in the
motivating application `f = H_D`, the Hilbert class polynomial of a CM
discriminant `D`, whose roots mod `p` are the `j`-invariants of elliptic curves
over `F_p` with CM by the order of discriminant `D`), the method computes

    gcd (f(j₀), N)

for evaluation points `j₀` and hopes for a nontrivial divisor.

The two results proved here are:

* `SingularModuli.gcd_eval_eq` — an *exact* product formula for
  `gcd (f(j₀), N)` in terms of the two divisibility predicates, hence
  `SingularModuli.gcd_nontrivial_iff`: the evaluation point succeeds **iff**
  `j₀` is a root of `f` modulo exactly one of `p`, `q` (an exclusive-or
  condition — this is the precise sense in which the method "works").

* `SingularModuli.card_goodSet` — an exact count of the successful residues
  modulo `N` via the Chinese Remainder decomposition:
  `r_p (q - r_q) + (p - r_p) r_q`, where `r_m` is the number of roots of
  `f` mod `m`.  Together with `card_rootsMod_le_natDegree` (`r_m ≤ deg f`)
  this is what drives the `√N` barrier proved in `SingularModuliBarrier.lean`.

Everything is stated for an arbitrary integer polynomial: no unproved property
of Hilbert class polynomials is assumed anywhere.
-/

open SingularModuli

open Polynomial Finset

/-! ## Roots modulo `m` -/





/-! ## The exact gcd formula -/



/-! ## Counting successful residues mod `N` -/





/-! ## Lab notes: worked instances with genuine Hilbert class polynomials

The class polynomials used below are the standard ones,
`H_{-3} = X`, `H_{-4} = X - 1728`, `H_{-7} = X + 3375`
(class number one: the singular moduli `0`, `1728`, `-3375`).
Each instance is certified twice: once as an explicit gcd computation, and once
as membership in `goodSet`, deduced from the general dictionary
`gcd_eval_nontrivial_iff` — so these really are instances of the theory above,
not standalone numerics. -/










open SingularModuli in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a : ℕ) :
    Nat.gcd a (p * q) = (if p ∣ a then p else 1) * (if q ∣ a then q else 1) := by
  have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  by_cases hpa : p ∣ a <;> by_cases hqa : q ∣ a
  · have : p * q ∣ a := hco.mul_dvd_of_dvd_of_dvd hpa hqa
    simp [hpa, hqa, Nat.gcd_eq_right this]
  · have hcq : Nat.Coprime q a := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqa
    have : Nat.gcd a (p * q) = Nat.gcd a p := Nat.Coprime.gcd_mul_right_cancel_right p hcq
    simp [hpa, hqa, this, Nat.gcd_eq_right hpa]
  · have hcp : Nat.Coprime p a := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
    have : Nat.gcd a (p * q) = Nat.gcd a q := Nat.Coprime.gcd_mul_left_cancel_right q hcp
    simp [hpa, hqa, this, Nat.gcd_eq_right hqa]
  · have hcp : Nat.Coprime p a := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpa
    have hcq : Nat.Coprime q a := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqa
    have h1 : Nat.gcd a (p * q) = Nat.gcd a q := Nat.Coprime.gcd_mul_left_cancel_right q hcp
    have h2 : Nat.gcd a q = 1 := hcq.symm
    simp [hpa, hqa, h1, h2]
