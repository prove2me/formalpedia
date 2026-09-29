-- Prove2me | Definitions.Def_Shared_ImmuneSemantics
-- name    : Shared_ImmuneSemantics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:56:47.101907+00:00
-- url     : https://prove2.me/theorems/963e36bb-ebe2-4c5e-92a3-4118609babc0
-- title:
--   Aether Catalog definitions — Shared_ImmuneSemantics
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneSemantics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneSemantics.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore

/-!
# Algorithmic Immune System, Part II: semantics, effects and self-execution

We equip the parasite calculus of Part I with a *total* denotational semantics
consisting of two layers:

* `PAst.eval t x` — the value computed by `t` when its input register holds `x`;
* `PAst.effect t x` — whether running `t` on input `x` *executes the forbidden
  action* `attack` (only the branch actually taken counts, so dead code is truly
  dead).

The runtime is *self-referential*: a program is always run on its own
attestation tag (`PAst.run t = PAst.effect t (PAst.code t)`), which is exactly
the ability of real self-modifying code to inspect its own source.  A program is
`malicious` when its self-execution performs the forbidden action.

Main results:

* `PAst.eval_const_of_inpFree` / `PAst.effect_const_of_inpFree`: programs without
  the self register are input-oblivious;
* `PAst.staticScan_correct`: the naive static scanner
  `staticScan t = effect t 0` is **sound and complete** on self-reference-free
  programs — the immune system wins outright in the absence of quining;
* `PAst.malicious_decidable_of_inpFree`: consequently maliciousness is decidable
  there.

Part III shows that both properties fail, unavoidably, once the self register is
available.
-/

namespace ImmuneSystem
namespace PAst

/-- Value semantics.  `x` is the content of the input (self) register. -/
def eval : PAst → ℕ → ℕ
  | inp, x => x
  | attack, _ => 1
  | lit n, _ => n
  | ite c a b, x => if eval c x ≠ 0 then eval a x else eval b x
  | call f a, x => eval f (eval a x)

/-- Effect semantics: `true` iff the forbidden action `attack` is actually
executed.  Only the branch that is really taken contributes. -/
def effect : PAst → ℕ → Bool
  | inp, _ => false
  | attack, _ => true
  | lit _, _ => false
  | ite c a b, x => effect c x || (if eval c x ≠ 0 then effect a x else effect b x)
  | call f a, x => effect a x || effect f (eval a x)



/-- Self-execution: the runtime feeds a program its own attestation tag. -/
def run (t : PAst) : Bool := effect t (code t)

/-- A program is *malicious* when its self-execution performs the forbidden
action.  This is a purely behavioural (semantic) notion. -/
def malicious (t : PAst) : Prop := run t = true

instance : DecidablePred malicious := fun t => by
  unfold malicious; infer_instance


/-- A program is *self-reference free* if it never reads the input register. -/
def inpFree : PAst → Bool
  | inp => false
  | attack => true
  | lit _ => true
  | ite c a b => inpFree c && inpFree a && inpFree b
  | call f a => inpFree f && inpFree a





/-! ### A benign padding family

`pad` is an exponentially large family of *semantically identical* benign
programs (all compute `0`, none has any effect).  It is the raw material both for
the immune-escape counting theorem of Part III and for the false-positive
counting theorem of Part IV. -/

/-- `pad l` is a chunk of dead code encoding the bit list `l`.  Every `pad l`
evaluates to `0` and is effect-free, yet distinct `l` give distinct ASTs. -/
def pad : List Bool → PAst
  | [] => lit 0
  | b :: bs => ite (lit 0) (lit (if b then 1 else 0)) (pad bs)





/-- The naive static scanner of the immune system: symbolically execute the
program on the neutral input. -/
def staticScan (t : PAst) : Bool := effect t 0



end PAst
end ImmuneSystem


