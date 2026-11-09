-- Prove2me | Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
-- name    : Couret_CertificateProofs_3244eb90a0e1
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:29.235884+00:00
-- url     : https://prove2.me/theorems/550b054f-7cea-4ce4-9b2b-31b66422084f
-- title:
--   Semantic and arithmetic interfaces for finite certificates
-- statement:
--   Defines the decoded state at a table index and the 146 noninitial decoded states. Defines strict-divisor residues, sorted arithmetic residue pairs, genuine factor pairs, concatenation of symbol words, observation machines and their runs, and the 101-class quotient observation machine. Strict divisors satisfy $d\mid n$ and $1<d<n$.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/CertificateProofs.lean; source file SHA-256 34105504de63d99f05e7d3427ba82853380bac1d8c053b618776cd7d98da83b2

import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

def decoded (i : StateId) : State Code30 := decode (entry i)





















def noninitialDecoded (i : Fin 146) : State Code30 := decoded i.succ









def strictDivisorResidue (n : Nat) (u : Code30) : Prop :=
  ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n ∧ d % 30 = residue30 u

def arithmeticPair (n : Nat) (a b : Symbol) : Prop :=
  strictDivisorResidue n (symbolCode a) ∧ strictDivisorResidue n (symbolCode b) ∧
  a.val ≤ b.val ∧ (residue30 (symbolCode a) * residue30 (symbolCode b)) % 30 = n % 30



def factorPair (n : Nat) (a b : Symbol) : Prop :=
  ∃ d e : Nat, 1 < d ∧ 1 < e ∧ d * e = n ∧
    d % 30 = residue30 (symbolCode a) ∧ e % 30 = residue30 (symbolCode b) ∧ a.val ≤ b.val



















def appendWord (u : Word Symbol) : Word Symbol → Word Symbol
  | .empty => u
  | .snoc v g => .snoc (appendWord u v) g



structure ObservationMachine (β : Type) where
  initial : β
  next : β → Symbol → β
  output : β → Nat

def machineRun {β : Type} (M : ObservationMachine β) (b : β) : Word Symbol → β
  | .empty => b
  | .snoc w g => M.next (machineRun M b w) g







def quotientMachine : ObservationMachine ClassId where
  initial := 0
  next := quotientNext
  output := quotientOutput





end Certificate
end Couret


