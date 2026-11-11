-- Prove2me | Definitions.Def_Couret_CausalFiber01_c81331552304
-- name    : Couret_CausalFiber01_c81331552304
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-10T13:15:12.857438+00:00
-- url     : https://prove2.me/theorems/6f8a4b45-8886-4375-8f20-e0c6e09bb36c
-- title:
--   Fibre reconstruction and finite authorization and recovery toy models
-- statement:
--   Defines fibre constancy and reconstruction on the witnessed image for maps between arbitrary types, together with uniform permission on observation fibres. The authorization toy model has four history constructors (timely, late, stale, missing); the first three produce a receipt, and only timely is authorized. Enriched observations explicitly pair the original observation with that Boolean verdict. The recovery toy model has worlds empty and committed, a constant unit observation, and actions execute, returnPrior and block. The required action is execute from empty and returnPrior after commit. Execute produces one effect from empty and two after commit; the other actions produce zero from empty and one after commit. These are mathematical toy definitions, not a verified implementation or a refinement of measured production traces.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad

/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

def FiberConstant {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V) : Prop :=
  ∀ a b : H, p a = p b → v a = v b





def ImageReconstructible {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V) : Prop :=
  ∃ r : (o : O) → (∃ h : H, p h = o) → V,
    ∀ h, v h = r (p h) ⟨h, rfl⟩



inductive History where
  | timely | late | stale | missing
  deriving DecidableEq, Repr

inductive Observation where
  | receipt | noReceipt
  deriving DecidableEq, Repr

def observe : History → Observation
  | .timely | .late | .stale => .receipt
  | .missing => .noReceipt

def authorized : History → Bool
  | .timely => true
  | .late | .stale | .missing => false






def enrichedObserve (h : History) : Observation × Bool :=
  (observe h, authorized h)

def enrichedReconstructor : Observation × Bool → Bool := Prod.snd









/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/
def UniformlyAllowed {H : Type u} {O : Type v}
    (p : H → O) (allowed : H → Prop) (o : O) : Prop :=
  ∀ h, p h = o → allowed h





/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery

inductive World where
  | empty | committed
  deriving DecidableEq, Repr

inductive Action where
  | execute | returnPrior | block
  deriving DecidableEq, Repr

def observation (_ : World) : Unit := ()

def required : World → Action
  | .empty => .execute
  | .committed => .returnPrior



def effects : World → Action → Nat
  | .empty, .execute => 1
  | .empty, _ => 0
  | .committed, .execute => 2
  | .committed, _ => 1







end Recovery


