-- Prove2me | Definitions.Def_Couret_SupportSemantics_a8ae2832b450
-- name    : Couret_SupportSemantics_a8ae2832b450
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:03.822117+00:00
-- url     : https://prove2.me/theorems/964127de-553e-45ce-afd2-8a7ab02384b6
-- title:
--   Position selections and commutative subproduct support
-- statement:
--   Defines finite words, position selections, their complements and products in a commutative monoid. Full support allows any selection; proper support requires selecting and omitting a position. Defines the initial/active support automaton and its semantic state. Specializes to natural multiplication and to $C_2\times C_4$ as the eight unit residues modulo 30, with coordinate addition representing residue multiplication.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/SupportSemantics.lean; source file SHA-256 d67147f5a0bd9f4d541f1eb4f8b15d92c422e93056e459a13a8312006a871dc3

import Std
import Std

/-!
COU-87, first semantic formalization, 2026-10-30.
The denotation uses independent choices of labeled occurrences, not the automaton
recurrence. Snoc words make appending an occurrence explicit. No assumption of
distinct factors is made. This file does not certify the 147/101 finite tables.
-/

universe u
namespace Couret

structure CMonoid (α : Type u) where
  one : α
  mul : α → α → α
  assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a

inductive Word (α : Type u) where
  | empty : Word α
  | snoc (w : Word α) (g : α) : Word α

variable {α : Type u}

def Word.nonempty : Word α → Prop
  | .empty => False
  | .snoc _ _ => True

def total (M : CMonoid α) : Word α → α
  | .empty => M.one
  | .snoc w g => M.mul (total M w) g

inductive Choice : Word α → Type u where
  | empty : Choice .empty
  | skip {w : Word α} (s : Choice w) (g : α) : Choice (.snoc w g)
  | take {w : Word α} (s : Choice w) (g : α) : Choice (.snoc w g)

namespace Choice

def picked : {w : Word α} → Choice w → Prop
  | _, .empty => False
  | _, .skip s _ => picked s
  | _, .take _ _ => True

def omitted : {w : Word α} → Choice w → Prop
  | _, .empty => False
  | _, .skip _ _ => True
  | _, .take s _ => omitted s

def eval (M : CMonoid α) : {w : Word α} → Choice w → α
  | _, .empty => M.one
  | _, .skip s _ => eval M s
  | _, .take s g => M.mul (eval M s) g

def allSkip : (w : Word α) → Choice w
  | .empty => .empty
  | .snoc w g => .skip (allSkip w) g

def allTake : (w : Word α) → Choice w
  | .empty => .empty
  | .snoc w g => .take (allTake w) g













def complement : {w : Word α} → Choice w → Choice w
  | _, .empty => .empty
  | _, .skip s g => .take (complement s) g
  | _, .take s g => .skip (complement s) g









end Choice

def fullSupport (M : CMonoid α) (w : Word α) (u : α) : Prop :=
  ∃ s : Choice w, Choice.eval M s = u

def properSupport (M : CMonoid α) (w : Word α) (u : α) : Prop :=
  ∃ s : Choice w, s.picked ∧ s.omitted ∧ Choice.eval M s = u









inductive State (α : Type u) where
  | initial : State α
  | active (r : α) (support : α → Prop) : State α

def step (M : CMonoid α) : State α → α → State α
  | .initial, g => .active g (fun _ => False)
  | .active r U, g => .active (M.mul r g)
      (fun u => U u ∨ (∃ v, U v ∧ M.mul g v = u) ∨ u = r ∨ u = g)

def semanticState (M : CMonoid α) : Word α → State α
  | .empty => .initial
  | .snoc w g => .active (total M (.snoc w g)) (properSupport M (.snoc w g))



def run (M : CMonoid α) : Word α → State α
  | .empty => .initial
  | .snoc w g => step M (run M w) g



def natProduct : CMonoid Nat where
  one := 1
  mul := Nat.mul
  assoc := Nat.mul_assoc
  comm := Nat.mul_comm
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one





def Word.atLeastTwo : Word Nat → Prop
  | .empty => True
  | .snoc w g => w.atLeastTwo ∧ 2 ≤ g







/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


abbrev Code30 := Fin 2 × Fin 4

def decForallFin : (n : Nat) → (P : Fin n → Prop) →
    ((i : Fin n) → Decidable (P i)) → Decidable (∀ i, P i)
  | 0, _, _ => isTrue (fun i => Fin.elim0 i)
  | n + 1, P, dp =>
    match dp 0, decForallFin n (fun i => P i.succ) (fun i => dp i.succ) with
    | isTrue h0, isTrue hs => isTrue (Fin.forall_fin_succ.mpr ⟨h0, hs⟩)
    | isFalse h0, _ => isFalse (fun h => h0 (h 0))
    | _, isFalse hs => isFalse (fun h => hs (fun i => h i.succ))

instance (n : Nat) (P : Fin n → Prop) [DecidablePred P] : Decidable (∀ i, P i) :=
  decForallFin n P (fun _ => inferInstance)

instance (P : Code30 → Prop) [DecidablePred P] : Decidable (∀ a, P a) :=
  match (inferInstance : Decidable (∀ a : Fin 2, ∀ b : Fin 4, P (a, b))) with
  | isTrue h => isTrue (fun ⟨a, b⟩ => h a b)
  | isFalse h => isFalse (fun h' => h (fun a b => h' (a, b)))

def mul30 (a b : Code30) : Code30 := (a.1 + b.1, a.2 + b.2)

def mod30Product : CMonoid Code30 where
  one := (0, 0)
  mul := mul30
  assoc := by decide
  comm := by decide
  one_mul := by decide
  mul_one := by decide

def residue30 (a : Code30) : Nat :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | 0, 1 => 7
  | 0, 2 => 19
  | 0, 3 => 13
  | 1, 0 => 11
  | 1, 1 => 17
  | 1, 2 => 29
  | 1, 3 => 23
  | _, _ => 1











end Couret


