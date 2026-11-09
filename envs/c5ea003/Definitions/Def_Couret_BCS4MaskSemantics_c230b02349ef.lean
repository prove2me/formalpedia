-- Prove2me | Definitions.Def_Couret_BCS4MaskSemantics_c230b02349ef
-- name    : Couret_BCS4MaskSemantics_c230b02349ef
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:48.964206+00:00
-- url     : https://prove2.me/theorems/f062fd1a-9e54-4175-9678-f71ca0764c57
-- title:
--   Finite residue-symbol and mask encoding
-- statement:
--   Defines eight symbols, masks from $0$ to $255$, and optional encoded states. A present state records a total residue and a support mask; an absent state decodes to the initial state. Provides residue-symbol conversion, bit membership, pair-presence and output counts, and the exact encoded step-validity relation. Pair presence requires both residues present, nondecreasing symbol order, and product equal to the total residue.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/MaskSemantics.lean; source file SHA-256 e62d6e7eba64af2437560f86dbb440160326ed6ca55e9e3151a62894e53af0c5; import module renamed from MaskSemantics to BCS4MaskSemantics to disambiguate source modules

import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-! Explicit decoding of the historical Python bit positions.
Bit positions follow [1,7,11,13,17,19,23,29], not lexicographic C2 x C4.
All finite facts below are checked by kernel `decide`.
-/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

def decExistsFin : (n : Nat) → (P : Fin n → Prop) →
    ((i : Fin n) → Decidable (P i)) → Decidable (∃ i, P i)
  | 0, _, _ => isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | n + 1, P, dp =>
    match dp 0, decExistsFin n (fun i => P i.succ) (fun i => dp i.succ) with
    | isTrue h0, _ => isTrue (Fin.exists_fin_succ.mpr (Or.inl h0))
    | _, isTrue hs => isTrue (Fin.exists_fin_succ.mpr (Or.inr hs))
    | isFalse h0, isFalse hs => isFalse (fun h =>
        (Fin.exists_fin_succ.mp h).elim h0 hs)

instance (n : Nat) (P : Fin n → Prop) [DecidablePred P] : Decidable (∃ i, P i) :=
  decExistsFin n P (fun _ => inferInstance)

instance (P : Code30 → Prop) [DecidablePred P] : Decidable (∃ a, P a) :=
  match (inferInstance : Decidable (∃ a : Fin 2, ∃ b : Fin 4, P (a,b))) with
  | isTrue h => isTrue (by rcases h with ⟨a,b,h⟩; exact ⟨(a,b),h⟩)
  | isFalse h => isFalse (fun ⟨a,ha⟩ => h ⟨a.1,a.2,ha⟩)

abbrev Symbol := Fin 8
abbrev Mask := Fin 256
abbrev EncodedState := Option (Symbol × Mask)

def symbolCode (g : Symbol) : Code30 :=
  match g.val with
  | 0 => (0,0)
  | 1 => (0,1)
  | 2 => (1,0)
  | 3 => (0,3)
  | 4 => (1,1)
  | 5 => (0,2)
  | 6 => (1,3)
  | _ => (1,2)

def codeSymbol (g : Code30) : Symbol :=
  match residue30 g with
  | 1 => 0
  | 7 => 1
  | 11 => 2
  | 13 => 3
  | 17 => 4
  | 19 => 5
  | 23 => 6
  | _ => 7






def contains (m : Mask) (g : Symbol) : Bool :=
  (m.val / (2 ^ g.val)) % 2 == 1

def encodeBits (b : Symbol → Bool) : Nat :=
  (if b 0 then 1 else 0) + (if b 1 then 2 else 0) +
  (if b 2 then 4 else 0) + (if b 3 then 8 else 0) +
  (if b 4 then 16 else 0) + (if b 5 then 32 else 0) +
  (if b 6 then 64 else 0) + (if b 7 then 128 else 0)



def maskSupport (m : Mask) (g : Code30) : Prop := contains m (codeSymbol g) = true

instance (m : Mask) : DecidablePred (maskSupport m) :=
  fun g => inferInstanceAs (Decidable (contains m (codeSymbol g) = true))



def decode : EncodedState → State Code30
  | none => .initial
  | some (r,m) => .active (symbolCode r) (maskSupport m)



def outputMask (s : EncodedState) : Nat :=
  match s with
  | none => 0
  | some (r,m) =>
    let bits := [0,1,2,3,4,5,6,7].map (fun (a : Symbol) =>
      if contains m a then 1 else 0)
    let fixed := [0,1,2,3,4,5,6,7].map (fun (a : Symbol) =>
      if contains m a && decide (mul30 (symbolCode a) (symbolCode a) = symbolCode r)
        then 1 else 0)
    (bits.sum + fixed.sum) / 2

def pairPresent (s : EncodedState) (a b : Symbol) : Bool :=
  match s with
  | none => false
  | some (r,m) => contains m a && contains m b && decide (a.val ≤ b.val) &&
    decide (mul30 (symbolCode a) (symbolCode b) = symbolCode r)

def presenceCount (s : EncodedState) : Nat :=
  ([0,1,2,3,4,5,6,7].map (fun (a : Symbol) =>
    ([0,1,2,3,4,5,6,7].map (fun (b : Symbol) =>
      if pairPresent s a b then 1 else 0)).sum)).sum



def StepValid (s t : EncodedState) (g : Symbol) : Prop :=
  match s,t with
  | none, some (r,m) => symbolCode r = symbolCode g ∧ ∀ u : Code30, ¬ maskSupport m u
  | some (r,m), some (r',m') =>
      symbolCode r' = mul30 (symbolCode r) (symbolCode g) ∧
      ∀ u : Code30, maskSupport m' u ↔
        maskSupport m u ∨
        (∃ v : Code30, maskSupport m v ∧ mul30 (symbolCode g) v = u) ∨
        u = symbolCode r ∨ u = symbolCode g
  | _, _ => False

instance (s t : EncodedState) (g : Symbol) : Decidable (StepValid s t g) := by
  cases s with
  | none => cases t with
    | none => exact isFalse (fun h => h)
    | some t =>
      rcases t with ⟨r,m⟩
      change Decidable (symbolCode r = symbolCode g ∧ ∀ u : Code30, ¬ maskSupport m u)
      infer_instance
  | some s =>
    rcases s with ⟨r,m⟩
    cases t with
    | none => exact isFalse (fun h => h)
    | some t =>
      rcases t with ⟨r',m'⟩
      change Decidable (symbolCode r' = mul30 (symbolCode r) (symbolCode g) ∧
        ∀ u : Code30, maskSupport m' u ↔ maskSupport m u ∨
          (∃ v : Code30, maskSupport m v ∧ mul30 (symbolCode g) v = u) ∨
          u = symbolCode r ∨ u = symbolCode g)
      infer_instance



end Certificate
end Couret


