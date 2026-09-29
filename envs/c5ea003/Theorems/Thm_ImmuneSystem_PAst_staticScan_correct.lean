-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_staticScan_correct
-- name    : ImmuneSystem.PAst.staticScan_correct
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:44:29.210986+00:00
-- url     : https://prove2.me/theorems/37726343-a804-44e2-be65-c52aa5d4e77d
-- title:
--   The immune system wins on non-quining code.
-- statement:
--   **The immune system wins on non-quining code.**  On self-reference-free
--   programs the static scanner is sound *and* complete for maliciousness.
--
--   ```lean
--   theorem ImmuneSystem.PAst.staticScan_correct{t : PAst} (h : inpFree t = true) : staticScan t = true ↔ malicious t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneSemantics.lean#L188

-- Thm stub generated from Shared/ImmuneSemantics.lean
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneSemantics

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

open ImmuneSystem
open PAst














/-! ### A benign padding family

`pad` is an exponentially large family of *semantically identical* benign
programs (all compute `0`, none has any effect).  It is the raw material both for
the immune-escape counting theorem of Part III and for the false-positive
counting theorem of Part IV. -/

theorem ImmuneSystem.PAst.staticScan_correct{t : PAst} (h : inpFree t = true) : staticScan t = true ↔ malicious t := by sorry
