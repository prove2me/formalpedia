-- Prove2me | Definitions.Def_Novelty_FactorialCRTObstruction
-- name    : Novelty_FactorialCRTObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:05.911866+00:00
-- url     : https://prove2.me/theorems/6a07eca5-61ff-465c-8df9-10f1565905a7
-- title:
--   Aether Catalog definitions — Novelty_FactorialCRTObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FactorialCRTObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FactorialCRTObstruction.lean by skeleton subtraction
import Mathlib

/-!
# A sharp low-stage obstruction to factorial CRT coordinates

Factorial digits have radices `1, 2, ..., k`, whose product is `k!`.  It is
therefore tempting to strengthen the mixed-radix bijection to an additive or
ring equivalence

`ZMod (k!) ≃ ZMod 2 × ... × ZMod k`.

This file proves that the strengthening works at `k = 3`, by the Chinese
remainder theorem, but already fails at `k = 4`.  The failure is stronger than
nonmultiplicativity: there is no additive equivalence.  Every element of
`ZMod 2 × ZMod 3 × ZMod 4` is killed by `12`, whereas `12` does not kill `1`
in `ZMod 24`.
-/

namespace FactorialCRTObstruction

/-- The nontrivial residue factors associated with factorial radices through
stage three.  (The omitted `ZMod 1` factor is a singleton.) -/
abbrev FactorialResidues3 := ZMod 2 × ZMod 3

/-- The nontrivial residue factors associated with factorial radices through
stage four. -/
abbrev FactorialResidues4 := ZMod 2 × ZMod 3 × ZMod 4

/-- At stage three, factorial residue coordinates really are CRT coordinates:
`3! = 2 * 3`, and the two nontrivial radices are coprime. -/
noncomputable def factorialThreeCRT :
    ZMod (Nat.factorial 3) ≃+* FactorialResidues3 :=
  (ZMod.ringEquivCongr (by decide)).trans
    (ZMod.chineseRemainder (by decide : Nat.Coprime 2 3))





end FactorialCRTObstruction


