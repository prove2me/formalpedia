-- Prove2me | solution 1 for SingularModuli.card_goodSet_eq_card_preimage
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:39.029199+00:00
-- url     : https://prove2.me/submissions/38e3efd8-7830-4a07-9343-634071985f6f

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    [NeZero p] [NeZero q] (f : Polynomial ℤ) :
    (Finset.univ.filter fun x : ZMod (p * q) =>
        ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq) x ∈ goodSet f p q).card
      = (goodSet f p q).card := by
  classical
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq)
  have : (Finset.univ.filter fun x : ZMod (p * q) => e x ∈ goodSet f p q)
      = Finset.univ.filter fun x : ZMod (p * q) => x ∈ (goodSet f p q).image e.symm := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx; exact ⟨e x, hx, by simp [e]⟩
    · rintro ⟨y, hy, rfl⟩; simpa [e] using hy
  rw [this, Finset.filter_mem_eq_inter]
  rw [Finset.univ_inter, Finset.card_image_of_injective _ e.symm.injective]
