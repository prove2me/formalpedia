-- Prove2me | Definitions.Def_Shared_ImmuneQuarantine
-- name    : Shared_ImmuneQuarantine
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:58:10.351079+00:00
-- url     : https://prove2.me/theorems/f11d81b2-9c74-41f8-94d8-25a648b2a68d
-- title:
--   Aether Catalog definitions — Shared_ImmuneQuarantine
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneQuarantine`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneQuarantine.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneSemantics

/-!
# Algorithmic Immune System, Part IV: attestation, quarantine and neutralization

Part III showed that *behavioural* detection of malice is impossible.  This part
shows what an immune system can nevertheless guarantee, and at what price.

The immune system is a **structural attestation monitor**: it stores a finite set
`tags` of attestation tags (Part I's Gödel numbers) of sanctioned program
variants and, after every mutation step of an *arbitrary, unknown, adversarial*
self-modification `adv : ℕ → PAst → PAst`, either accepts the mutant (its tag is
sanctioned) or rolls back to the trusted baseline.

Main results:

* `verify_iff_mem` — tag-based verification is exactly membership in the
  sanctioned set: attestation has **no collisions** (uses `code_injective`);
* `quarantine_mem`, `quarantine_idem` — quarantine is an idempotent retraction
  onto the sanctioned set;
* `trace_mem` — **containment**: whatever the adversary does, at every time step
  the running program is sanctioned;
* `neutralization` — **the headline theorem**: if every sanctioned variant is
  harmless, then no forbidden action is ever executed, for every adversary and
  all time;
* `alarm_iff_escape`, `rollback` — detection is *complete*: every unsanctioned
  mutation, however unknown, raises an alarm at the step it occurs and is
  reverted immediately;
* `finite_whitelist_rejects_benign`, `benign_rejection_card` — **the price**: any
  finite attestation whitelist rejects infinitely many, and at least
  `2 ^ n - |S|` of size `≤ 3n+1`, semantically benign refactorings;
* `immune_conservation` — the synthesis: perfect containment, exponential
  rigidity, and no perfect behavioural detector, in one statement.
-/

namespace ImmuneSystem
namespace PAst

open Finset

section Attestation

variable (S : Finset PAst)

/-- The attestation database: the tags of the sanctioned variants. -/
def tags : Finset ℕ := S.image code

/-- The monitor's verification step: recompute the tag of the running AST and
look it up in the attestation database. -/
def verify (t : PAst) : Prop := code t ∈ tags S

instance (t : PAst) : Decidable (verify S t) := by
  unfold verify; infer_instance


end Attestation

/-- The quarantine operator: accept a sanctioned mutant, otherwise roll back to
the trusted baseline `b`. -/
def quarantine (S : Finset PAst) (b t : PAst) : PAst := if t ∈ S then t else b






/-- The guarded execution trace under an **arbitrary, unknown, time-dependent
self-modification** `adv`.  At each step the adversary rewrites the running AST
however it likes; the monitor then verifies and, if necessary, rolls back. -/
def trace (S : Finset PAst) (b : PAst) (adv : ℕ → PAst → PAst) : ℕ → PAst
  | 0 => b
  | n + 1 => quarantine S b (adv n (trace S b adv n))





/-- The alarm raised by the monitor at step `n`. -/
def alarm (S : Finset PAst) (b : PAst) (adv : ℕ → PAst → PAst) (n : ℕ) : Prop :=
  ¬ verify S (adv n (trace S b adv n))




/-! ### The price of structural attestation

Attestation is *syntactic*, while program behaviour is *semantic*.  The gap is
not a small one: any finite whitelist rejects an infinite, indeed exponentially
dense, family of semantically identical benign programs. -/

/-- The `n`-bit family of benign padded variants. -/
noncomputable def padFamily (n : ℕ) : Finset PAst :=
  Finset.image (fun v : Fin n → Bool => pad (List.ofFn v)) Finset.univ





/-! ### Synthesis -/


end PAst
end ImmuneSystem


