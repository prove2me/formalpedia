-- Prove2me | Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
-- name    : Couret_BCS5MaskSemantics_646df6f48a3c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:44.860165+00:00
-- url     : https://prove2.me/theorems/40e9a787-a6ec-41ca-8bf9-7f851a6555f5
-- title:
--   Eight-bit residue-mask automaton
-- statement:
--   Unit residue codes modulo 30 are assigned bit positions in the historical order $1,7,11,13,17,19,23,29$. A mask records support by its corresponding bits, singleton masks are powers of two, and shifting multiplies represented residues. The update combines old, shifted, total-product, and appended singleton contributions. Distinct initial and active constructors, decoding, canonicality and word iteration supply the finite implementation interface.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/MaskSemantics.lean; source file SHA-256 2b99a0c723013ccd7334d8463e5afb270be06050a7f31c47da8e9c55060a5eb7; import module renamed from MaskSemantics to BCS5MaskSemantics to disambiguate source modules

import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret

def pythonAlphabet : List Code30 :=
  [(0,0),(0,1),(1,0),(0,3),(1,1),(0,2),(1,3),(1,2)]

def bitIndex30 (a : Code30) : Nat :=
  match a.1.val, a.2.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 1, 0 => 2
  | 0, 3 => 3
  | 1, 1 => 4
  | 0, 2 => 5
  | 1, 3 => 6
  | 1, 2 => 7
  | _, _ => 0









def codeOfBit (i : Fin 8) : Code30 :=
  match i.val with
  | 0 => (0,0)
  | 1 => (0,1)
  | 2 => (1,0)
  | 3 => (0,3)
  | 4 => (1,1)
  | 5 => (0,2)
  | 6 => (1,3)
  | _ => (1,2)



def maskSupport (mask : Nat) (u : Code30) : Prop :=
  mask.testBit (bitIndex30 u) = true

instance (mask : Nat) (u : Code30) : Decidable (maskSupport mask u) :=
  inferInstanceAs (Decidable (mask.testBit (bitIndex30 u) = true))

def singletonMask (u : Code30) : Nat := 2 ^ bitIndex30 u











def shiftMaskOn (g : Code30) (mask : Nat) : List Code30 → Nat
  | [] => 0
  | a :: rest =>
      (if maskSupport mask a then singletonMask (mul30 g a) else 0) |||
        shiftMaskOn g mask rest

def shiftMask (g : Code30) (mask : Nat) : Nat := shiftMaskOn g mask pythonAlphabet







def nextMask (r : Code30) (mask : Nat) (g : Code30) : Nat :=
  mask ||| shiftMask g mask ||| singletonMask r ||| singletonMask g





inductive MaskState where
  | initial : MaskState
  | active (r : Code30) (mask : Nat) : MaskState
  deriving DecidableEq

def maskStep : MaskState → Code30 → MaskState
  | .initial, g => .active g 0
  | .active r mask, g => .active (mul30 r g) (nextMask r mask g)

def decodeMaskState : MaskState → State Code30
  | .initial => .initial
  | .active r mask => .active r (maskSupport mask)

def MaskState.canonical : MaskState → Prop
  | .initial => True
  | .active _ mask => mask < 256







def maskRun : Word Code30 → MaskState
  | .empty => .initial
  | .snoc w g => maskStep (maskRun w) g



















end Couret


