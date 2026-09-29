-- Prove2me | Theorems.Thm_SingularModuli_card_goodSet_eq_card_preimage
-- name    : SingularModuli.card_goodSet_eq_card_preimage
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:12.307135+00:00
-- url     : https://prove2.me/theorems/e34999a7-a218-4e2c-90cd-0abc44627676
-- title:
--   The CRT coordinates exhaust all residues: the number of successful residues
-- statement:
--   The CRT coordinates exhaust all residues: the number of successful residues
--   mod `N` really is `card_goodSet`, computed in `ZMod N` itself.
--
--   ```lean
--   theorem SingularModuli.card_goodSet_eq_card_preimage{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       [NeZero p] [NeZero q] (f : Polynomial ℤ) :
--       (Finset.univ.filter fun x : ZMod (p * q) =>
--           ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq) x ∈ goodSet f p q).card
--         = (goodSet f p q).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliCore.lean#L152

-- Thm stub generated from Geometry/SingularModuliCore.lean
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

theorem SingularModuli.card_goodSet_eq_card_preimage{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    [NeZero p] [NeZero q] (f : Polynomial ℤ) :
    (Finset.univ.filter fun x : ZMod (p * q) =>
        ZMod.chineseRemainder ((Nat.coprime_primes hp hq).mpr hpq) x ∈ goodSet f p q).card
      = (goodSet f p q).card := by sorry
