-- Prove2me | Definitions.Def_Cryptography_ClosureOneWay
-- name    : Cryptography_ClosureOneWay
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:16.891855+00:00
-- url     : https://prove2.me/theorems/d816d6f5-340e-419a-b14b-3f2f94ded64d
-- title:
--   Aether Catalog definitions — Cryptography_ClosureOneWay
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ClosureOneWay`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ClosureOneWay.lean by skeleton subtraction
import Mathlib

/-!
# EML Closure One-Way Functions

Formalizes **self-referential cryptography**: bridging order-theoretic
closure operators with cryptographic protocol design.

## Bridge: Order Theory → Cryptography

- `closureMin x = min(cl({x}))` — one-way function candidate
- Idempotence enables zero-knowledge simulation
- Fixed points define the "hard language"
-/

set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace EMLCrypto

/-- Closure operator with extensiveness, monotonicity, idempotence.
    Bridge: order theory → cryptography. -/
class EMLClosureOperator (C : Type*) where
  cl : Set C → Set C
  extensive : ∀ (A : Set C), A ⊆ cl A
  mono : ∀ {A B : Set C}, A ⊆ B → cl A ⊆ cl B
  idem : ∀ (A : Set C), cl (cl A) = cl A

variable {C : Type*}

section SetLevel
variable [EMLClosureOperator C]

theorem self_mem_closure (x : C) :
    x ∈ EMLClosureOperator.cl ({x} : Set C) :=
  EMLClosureOperator.extensive {x} rfl





def IsClosed (A : Set C) : Prop :=
  EMLClosureOperator.cl A = A




end SetLevel

section ClosureMin
variable [EMLClosureOperator C] [Fintype C] [LinearOrder C]

omit [LinearOrder C] in
private theorem closure_singleton_nonempty (x : C) :
    (Finset.univ.filter (fun y => y ∈ EMLClosureOperator.cl ({x} : Set C))).Nonempty :=
  ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, self_mem_closure x⟩⟩

/-- The **closure min**: maps x to min(cl({x})).
    Bridge: order theory → cryptography (one-way function). -/
def closureMin (x : C) : C :=
  (Finset.univ.filter (fun y => y ∈ EMLClosureOperator.cl ({x} : Set C))).min'
    (closure_singleton_nonempty x)















end ClosureMin

/-! ## Identity Closure -/

instance identityClosure (C : Type*) : EMLClosureOperator C where
  cl := id
  extensive := fun _ => Set.Subset.rfl
  mono := fun h => h
  idem := fun _ => rfl


/-! ## Sigma Protocol -/


section SigmaProtocol
variable [EMLClosureOperator C] [Fintype C] [LinearOrder C]

def sigmaCommit (r : C) : C := closureMin r

def sigmaRespond (r : C) (e : Bool) : C :=
  if e then closureMin r else r

def sigmaVerify (a : C) (e : Bool) (z : C) : Prop :=
  if e then z = a else closureMin z = a









end SigmaProtocol

/-! ## Key Exchange -/

structure FixedPointKeyExchange (C : Type*) [LinearOrder C] [Fintype C] where
  cl_A : EMLClosureOperator C
  cl_B : EMLClosureOperator C
  secret_A : C
  secret_B : C

section KeyExchange
variable [LinearOrder C] [Fintype C]

def FixedPointKeyExchange.pubA (kex : FixedPointKeyExchange C) : C :=
  @closureMin C kex.cl_A _ _ kex.secret_A

def FixedPointKeyExchange.pubB (kex : FixedPointKeyExchange C) : C :=
  @closureMin C kex.cl_B _ _ kex.secret_B

def FixedPointKeyExchange.ssA (kex : FixedPointKeyExchange C) : C :=
  @closureMin C kex.cl_A _ _ kex.pubB

def FixedPointKeyExchange.ssB (kex : FixedPointKeyExchange C) : C :=
  @closureMin C kex.cl_B _ _ kex.pubA





end KeyExchange

/-! ## Commuting Closures -/

def CommutingClosures (cl_A cl_B : EMLClosureOperator C) : Prop :=
  ∀ (A : Set C), cl_A.cl (cl_B.cl A) = cl_B.cl (cl_A.cl A)



/-! ## One-Way Function Structure -/

structure ClosureOWF (C : Type*) [LinearOrder C] [Fintype C]
    extends EMLClosureOperator C where
  surj_fixed : ∀ y : C,
    @closureMin C toEMLClosureOperator _ _ y = y →
    ∃ x, @closureMin C toEMLClosureOperator _ _ x = y

def ClosureOWF.f [LinearOrder C] [Fintype C] (owf : ClosureOWF C) : C → C :=
  @closureMin C owf.toEMLClosureOperator _ _



/-! ## Protocol Instance -/

section ProtocolInstance
variable [EMLClosureOperator C] [Fintype C] [LinearOrder C]

structure IdempotentSigmaProtocol where
  target : C
  witness : C
  valid : closureMin witness = target




end ProtocolInstance

end EMLCrypto
end


