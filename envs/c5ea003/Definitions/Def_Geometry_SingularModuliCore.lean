-- Prove2me | Definitions.Def_Geometry_SingularModuliCore
-- name    : Geometry_SingularModuliCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:39.043595+00:00
-- url     : https://prove2.me/theorems/d0ff1e07-eff5-4bae-83dc-db9d8a56072c
-- title:
--   Aether Catalog definitions — Geometry_SingularModuliCore
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SingularModuliCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SingularModuliCore.lean by skeleton subtraction
import Mathlib
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

namespace SingularModuli

open Polynomial Finset

/-! ## Roots modulo `m` -/

/-- The finite set of roots in `ZMod m` of the reduction of an integer
polynomial `f`. In the motivating case `f = H_D` and `m = p` a prime split in
the CM field, this is the set of `j`-invariants over `F_p` with CM by the order
of discriminant `D`; its cardinality is the class number `h(D)`. -/
noncomputable def rootsMod (f : Polynomial ℤ) (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.filter fun x => (f.map (Int.castRingHom (ZMod m))).eval x = 0




/-! ## The exact gcd formula -/



/-! ## Counting successful residues mod `N` -/

/-- The set of successful residues, written in Chinese-Remainder coordinates
`ZMod p × ZMod q`: an evaluation point succeeds iff it is a root modulo exactly
one of the primes. -/
noncomputable def goodSet (f : Polynomial ℤ) (p q : ℕ) [NeZero p] [NeZero q] : Finset (ZMod p × ZMod q) :=
  Finset.univ.filter fun z => Xor (z.1 ∈ rootsMod f p) (z.2 ∈ rootsMod f q)




/-! ## Lab notes: worked instances with genuine Hilbert class polynomials

The class polynomials used below are the standard ones,
`H_{-3} = X`, `H_{-4} = X - 1728`, `H_{-7} = X + 3375`
(class number one: the singular moduli `0`, `1728`, `-3375`).
Each instance is certified twice: once as an explicit gcd computation, and once
as membership in `goodSet`, deduced from the general dictionary
`gcd_eval_nontrivial_iff` — so these really are instances of the theory above,
not standalone numerics. -/

/-- `H_{-3} = X`, the singular modulus `j = 0`. -/
noncomputable def hilbertNeg3 : Polynomial ℤ := Polynomial.X

/-- `H_{-4} = X - 1728`, the singular modulus `j = 1728`. -/
noncomputable def hilbertNeg4 : Polynomial ℤ := Polynomial.X - Polynomial.C 1728

/-- `H_{-7} = X + 3375`, the singular modulus `j = -3375`. -/
noncomputable def hilbertNeg7 : Polynomial ℤ := Polynomial.X + Polynomial.C 3375






end SingularModuli


