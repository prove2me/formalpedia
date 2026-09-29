-- Prove2me | Theorems.Thm_SingularModuli_card_goodSet
-- name    : SingularModuli.card_goodSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:17.958063+00:00
-- url     : https://prove2.me/theorems/030ec96f-6992-4628-93c1-62f51504a98a
-- title:
--   Exact count of successful residues.
-- statement:
--   **Exact count of successful residues.**  With `r_p`, `r_q` the numbers of
--   roots of `f` mod `p`, `q`, exactly `r_p (q - r_q) + (p - r_p) r_q` of the `p q`
--   residues modulo `N` yield a nontrivial factor.
--
--   ```lean
--   theorem SingularModuli.card_goodSet(f : Polynomial ℤ) (p q : ℕ) [NeZero p] [NeZero q] :
--       (goodSet f p q).card =
--         (rootsMod f p).card * (q - (rootsMod f q).card)
--           + (p - (rootsMod f p).card) * (rootsMod f q).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SingularModuliCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SingularModuliCore.lean#L130

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

theorem SingularModuli.card_goodSet(f : Polynomial ℤ) (p q : ℕ) [NeZero p] [NeZero q] :
    (goodSet f p q).card =
      (rootsMod f p).card * (q - (rootsMod f q).card)
        + (p - (rootsMod f p).card) * (rootsMod f q).card := by sorry
