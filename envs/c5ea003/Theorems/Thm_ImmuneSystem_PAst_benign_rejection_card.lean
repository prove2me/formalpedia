-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_benign_rejection_card
-- name    : ImmuneSystem.PAst.benign_rejection_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:43:02.017022+00:00
-- url     : https://prove2.me/theorems/4a0caa79-3d74-4398-b653-be56aeebb44a
-- title:
--   Exponential false-rejection bound.
-- statement:
--   **Exponential false-rejection bound.**  A whitelist of size `|S|` rejects at
--   least `2 ^ n - |S|` benign programs of size at most `3n + 1`: sound structural
--   attestation buys containment at the cost of exponential rigidity.
--
--   ```lean
--   theorem ImmuneSystem.PAst.benign_rejection_card(S : Finset PAst) (n : ℕ) :
--       2 ^ n - S.card ≤ (padFamily n \ S).card ∧
--         ∀ t ∈ padFamily n \ S, (∀ x, effect t x = false) ∧ size t ≤ 3 * n + 1 := by sorry
--   /-! ### Synthesis -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneQuarantine.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneQuarantine.lean#L201

-- Thm stub generated from Shared/ImmuneQuarantine.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneDetection
import Definitions.Def_Shared_ImmuneQuarantine
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

open ImmuneSystem
open PAst

open Finset


variable (S : Finset PAst)





















/-! ### The price of structural attestation

Attestation is *syntactic*, while program behaviour is *semantic*.  The gap is
not a small one: any finite whitelist rejects an infinite, indeed exponentially
dense, family of semantically identical benign programs. -/

theorem ImmuneSystem.PAst.benign_rejection_card(S : Finset PAst) (n : ℕ) :
    2 ^ n - S.card ≤ (padFamily n \ S).card ∧
      ∀ t ∈ padFamily n \ S, (∀ x, effect t x = false) ∧ size t ≤ 3 * n + 1 := by sorry
