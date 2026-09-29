-- Prove2me | Definitions.Def_Shared_ImmuneOracle
-- name    : Shared_ImmuneOracle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:59:30.094961+00:00
-- url     : https://prove2.me/theorems/128fb9b7-8952-4a42-8d6a-d0772b34bafe
-- title:
--   Aether Catalog definitions — Shared_ImmuneOracle
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneOracle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneOracle.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneQuarantine

/-!
# Algorithmic Immune System, Part V: the reflexive oracle barrier

Part III proved that no *program* of the parasite calculus can be a sound and
complete behavioural detector.  A natural objection is that this might be a
limitation of computational power: perhaps a sufficiently strong immune system —
one with unbounded, even hypercomputational, analysis capability — could succeed.

Here we refute that objection in the strongest possible form.  We extend the
calculus with a primitive `ask` that queries an **arbitrary function**
`O : ℕ → ℕ` (the immune oracle: no computability whatsoever is assumed) on a
computed attestation tag, and we let programs use it freely.  Then:

* `no_correct_reflexive_oracle` — **for every** `O : ℕ → ℕ` there is a program
  whose behaviour `O` misdescribes.  Reflexivity, not computational power, is the
  barrier;
* `askFree_eval_oracle_indep`, `askFree_effect_oracle_indep` — programs that do
  not consult the immune system have oracle-independent behaviour;
* `oracle_correct_on_askFree` — and for those programs a correct (noncomputably
  defined) oracle *does* exist.

Together (`reflexive_dichotomy`) this locates the exact frontier: an immune
system can be perfectly correct about code that ignores it, and is necessarily
wrong about code that watches it.
-/

namespace ImmuneSystem

/-- ASTs of the *reflexive* calculus: as in Part I, but subprogram invocation is
replaced by `ask`, a query to the immune oracle. -/
inductive OAst : Type
  | inp : OAst
  | attack : OAst
  | lit : ℕ → OAst
  | ite : OAst → OAst → OAst → OAst
  | ask : OAst → OAst
  deriving DecidableEq, Repr

namespace OAst

/-- Attestation tag for reflexive ASTs. -/
def codeO : OAst → ℕ
  | inp => 0
  | attack => 1
  | lit n => 5 * n + 2
  | ite c a b => 5 * (Nat.pair (Nat.pair (codeO c) (codeO a)) (codeO b)) + 3
  | ask a => 5 * codeO a + 4



variable (O : ℕ → ℕ)

/-- Value semantics relative to an arbitrary immune oracle `O`. -/
def evalO : OAst → ℕ → ℕ
  | inp, x => x
  | attack, _ => 1
  | lit n, _ => n
  | ite c a b, x => if evalO c x ≠ 0 then evalO a x else evalO b x
  | ask a, x => O (evalO a x)

/-- Effect semantics relative to `O`.  Consulting the immune system is itself
harmless; only `attack` on an executed branch counts. -/
def effectO : OAst → ℕ → Bool
  | inp, _ => false
  | attack, _ => true
  | lit _, _ => false
  | ite c a b, x => effectO c x || (if evalO O c x ≠ 0 then effectO a x else effectO b x)
  | ask a, x => effectO a x



/-- Self-execution in the reflexive calculus. -/
def maliciousO (t : OAst) : Prop := effectO O t (codeO t) = true

/-- The oracle is *correct* if its verdict on every attestation tag matches the
actual behaviour of the corresponding program **in the world containing the
oracle itself**. -/
def OracleCorrect : Prop := ∀ t : OAst, (O (codeO t) ≠ 0 ↔ maliciousO O t)

/-- The reflexive parasite: it asks the immune oracle about its own tag and
attacks exactly when it is cleared. -/
def refParasite : OAst := ite (ask inp) (lit 0) attack



/-- Programs that never consult the immune system. -/
def askFree : OAst → Bool
  | inp => true
  | attack => true
  | lit _ => true
  | ite c a b => askFree c && askFree a && askFree b
  | ask _ => false





open Classical in
/-- The canonical immune oracle: it flags a tag iff that tag belongs to a
non-reflexive malicious program.  (Defined by unrestricted comprehension: no
computability is claimed, and none is needed.) -/
noncomputable def canonicalOracle : ℕ → ℕ := fun n =>
  if ∃ t : OAst, codeO t = n ∧ askFree t = true ∧ maliciousO (fun _ => 0) t then 1 else 0



end OAst
end ImmuneSystem


