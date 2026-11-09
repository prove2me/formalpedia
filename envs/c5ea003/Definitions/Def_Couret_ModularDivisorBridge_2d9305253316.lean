-- Prove2me | Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
-- name    : Couret_ModularDivisorBridge_2d9305253316
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:32.930481+00:00
-- url     : https://prove2.me/theorems/13fcef7c-55dc-42dc-a60e-82f4d484cd71
-- title:
--   Mapping selections to unit-residue coordinates
-- statement:
--   Defines mapping of words and their selections, and pullback of mapped selections. Encodes a natural number by its residue modulo 30 into $C_2\times C_4$, using the eight unit residues and a default identity code for other residues. Defines the predicate that all factors in a natural word are coprime to 30. Subsequent correctness claims require the appropriate coprimality hypotheses.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41

import Std
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret

def Word.map {α : Type v} {β : Type v} (f : α → β) : Word α → Word β
  | .empty => .empty
  | .snoc w g => .snoc (w.map f) (f g)

namespace Choice

def map {α : Type v} {β : Type v} (f : α → β) :
    {w : Word α} → Choice w → Choice (w.map f)
  | _, .empty => .empty
  | _, .skip s g => .skip (map f s) (f g)
  | _, .take s g => .take (map f s) (f g)

def pullback {α : Type v} {β : Type v} (f : α → β) :
    (w : Word α) → Choice (w.map f) → Choice w
  | .empty, .empty => .empty
  | .snoc w g, .skip s _ => .skip (pullback f w s) g
  | .snoc w g, .take s _ => .take (pullback f w s) g







end Choice

def rawCode30 (r : Nat) : Code30 :=
  match r with
  | 1 => (0, 0)
  | 7 => (0, 1)
  | 19 => (0, 2)
  | 13 => (0, 3)
  | 11 => (1, 0)
  | 17 => (1, 1)
  | 29 => (1, 2)
  | 23 => (1, 3)
  | _ => (0, 0)

def encode30 (n : Nat) : Code30 := rawCode30 (n % 30)







def Word.coprime30Factors : Word Nat → Prop
  | .empty => True
  | .snoc w p => w.coprime30Factors ∧ Nat.gcd p 30 = 1





























end Couret


