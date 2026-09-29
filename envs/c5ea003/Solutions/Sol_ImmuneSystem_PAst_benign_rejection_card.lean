-- Prove2me | solution 1 for ImmuneSystem.PAst.benign_rejection_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:17:13.953733+00:00
-- url     : https://prove2.me/submissions/e1fb2319-d67f-4857-bcd5-80dbbf1a50e7

-- Sol generated from Shared/ImmuneQuarantine.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneQuarantine
import Definitions.Def_Shared_ImmuneSemantics
import Theorems.Thm_ImmuneSystem_PAst_card_padFamily
import Theorems.Thm_ImmuneSystem_PAst_padFamily_benign

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
theorem solution(S : Finset PAst) (n : ℕ) :
    2 ^ n - S.card ≤ (padFamily n \ S).card ∧
      ∀ t ∈ padFamily n \ S, (∀ x, effect t x = false) ∧ size t ≤ 3 * n + 1 := by
  constructor
  · have := Finset.le_card_sdiff S (padFamily n)
    rwa [card_padFamily n] at this
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := padFamily_benign (Finset.mem_sdiff.1 ht).1
    exact ⟨h2, h3⟩
