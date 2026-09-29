-- Prove2me | solution 1 for ImmuneSystem.PAst.neutralization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:26:07.603077+00:00
-- url     : https://prove2.me/submissions/54bbe217-a0ad-4f6d-89d2-327ba3c18f09

-- Sol generated from Shared/ImmuneQuarantine.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneQuarantine
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_trace_mem

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

open ImmuneSystem
open PAst

open Finset


variable (S : Finset PAst)





















/-! ### The price of structural attestation

Attestation is *syntactic*, while program behaviour is *semantic*.  The gap is
not a small one: any finite whitelist rejects an infinite, indeed exponentially
dense, family of semantically identical benign programs. -/






/-! ### Synthesis -/



open ImmuneSystem.PAst in
theorem solution{S : Finset PAst} {b : PAst} (hb : b ∈ S)
    (hsafe : ∀ t ∈ S, ¬ malicious t) (adv : ℕ → PAst → PAst) (n : ℕ) :
    ¬ malicious (trace S b adv n) :=
  hsafe _ (trace_mem hb adv n)
