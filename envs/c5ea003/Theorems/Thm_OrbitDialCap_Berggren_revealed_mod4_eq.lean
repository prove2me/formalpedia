-- Prove2me | Theorems.Thm_OrbitDialCap_Berggren_revealed_mod4_eq
-- name    : OrbitDialCap.Berggren.revealed_mod4_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:16.669983+00:00
-- url     : https://prove2.me/theorems/3341dd8e-45ac-486f-969e-c6728e97138d
-- title:
--   N-invariance of the orbit dial.
-- statement:
--   **N-invariance of the orbit dial.**  The revealed set mod `4` is exactly the fixed
--   two-element set `{(1,0,1), (3,0,1)}`.  It is a constant of the tree, not a function of
--   any target: an orbit dial built from it is one universal exclusion table.
--
--   ```lean
--   theorem OrbitDialCap.Berggren.revealed_mod4_eq:
--       revealedMod4 =
--         {((1 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4)), ((3 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4))} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/OrbitDialInvariants.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/OrbitDialInvariants.lean#L90

-- Thm stub generated from Tropical/OrbitDialInvariants.lean
import Mathlib
import Definitions.Def_Tropical_OrbitDialInvariants

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

open OrbitDialCap
open Berggren

theorem OrbitDialCap.Berggren.revealed_mod4_eq:
    revealedMod4 =
      {((1 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4)), ((3 : ZMod 4), (0 : ZMod 4), (1 : ZMod 4))} := by sorry
