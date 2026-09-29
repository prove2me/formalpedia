-- Prove2me | Definitions.Def_Tropical_OrbitDialInvariants
-- name    : Tropical_OrbitDialInvariants
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:17.662128+00:00
-- url     : https://prove2.me/theorems/e1bcb7cb-1c95-43e6-bb0a-5dbd31c1c076
-- title:
--   Aether Catalog definitions — Tropical_OrbitDialInvariants
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.OrbitDialInvariants`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/OrbitDialInvariants.lean by skeleton subtraction
import Mathlib

/-!
# Berggren-tree orbit invariants: the revealed residue set is universal

This file formalises the *characterisation arm* of the ORBIT-DIAL-CAP-TEST
(FACT round-74 #2, exp 564): the residues revealed by the root component of the
Berggren triplet tree are fixed once and for all, so the "orbit dial" they define is
the same table for every semiprime `N`.

## Contents

* `OrbitDialCap.Berggren.InTree` — the root component of the Berggren tree, generated
  from `(3,4,5)` by the three unimodular matrices `B₁, B₂, B₃`.
* `OrbitDialCap.Berggren.inTree_isPT` — every node is a Pythagorean triple.
* `OrbitDialCap.Berggren.inTree_congruence` — the congruence invariant of the whole
  component: `a` odd, `4 ∣ b`, `c ≡ 1 (mod 4)`.
* `OrbitDialCap.Berggren.revealed_mod4_eq` — **the revealed residue set mod 4 is the
  fixed two-element set `{(1,0,1), (3,0,1)}`**, hence carries no parameter dependence:
  the orbit dial is one universal exclusion table.
* `OrbitDialCap.Berggren.three_dvd_leg_mul` — barrier 6 restated as a primitive-triple
  congruence: `3` divides a leg of every Pythagorean triple.
* `OrbitDialCap.Berggren.parity_dial_sound` — the bridge to factoring: the parity skip
  never discards a divisor of an odd `N`, i.e. it has soundness `s = 1`.
-/

namespace OrbitDialCap
namespace Berggren

/-- An integer Pythagorean triple. -/
def IsPT (t : ℤ × ℤ × ℤ) : Prop := t.1 ^ 2 + t.2.1 ^ 2 = t.2.2 ^ 2

/-- First Berggren matrix `[[1,-2,2],[2,-1,2],[2,-2,3]]`. -/
def B1 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 - 2 * t.2.1 + 2 * t.2.2, 2 * t.1 - t.2.1 + 2 * t.2.2, 2 * t.1 - 2 * t.2.1 + 3 * t.2.2)

/-- Second Berggren matrix `[[1,2,2],[2,1,2],[2,2,3]]`. -/
def B2 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (t.1 + 2 * t.2.1 + 2 * t.2.2, 2 * t.1 + t.2.1 + 2 * t.2.2, 2 * t.1 + 2 * t.2.1 + 3 * t.2.2)

/-- Third Berggren matrix `[[-1,2,2],[-2,1,2],[-2,2,3]]`. -/
def B3 (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (-t.1 + 2 * t.2.1 + 2 * t.2.2, -2 * t.1 + t.2.1 + 2 * t.2.2, -2 * t.1 + 2 * t.2.1 + 3 * t.2.2)

/-- The root component of the Berggren tree: the orbit of `(3,4,5)` under the three
Berggren moves.  This is exactly the set of nodes enumerated by the experiment's
root BFS. -/
inductive InTree : ℤ × ℤ × ℤ → Prop
  | root : InTree (3, 4, 5)
  | step1 {t} : InTree t → InTree (B1 t)
  | step2 {t} : InTree t → InTree (B2 t)
  | step3 {t} : InTree t → InTree (B3 t)




/-- The revealed residue set of the root component, projected to `ZMod 4`. -/
def revealedMod4 : Set (ZMod 4 × ZMod 4 × ZMod 4) :=
  {r | ∃ t, InTree t ∧ r = ((t.1 : ZMod 4), (t.2.1 : ZMod 4), (t.2.2 : ZMod 4))}







/-- The parity dial's *kept set*, as a family indexed by the target `N`. -/
def parityKept : ℕ → Set ℕ := fun _ => {p | ¬ (2 ∣ p)}




end Berggren
end OrbitDialCap


