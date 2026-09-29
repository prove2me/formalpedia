-- Prove2me | Theorems.Thm_ImmuneSystem_PAst_pad_injective
-- name    : ImmuneSystem.PAst.pad_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:42:29.794985+00:00
-- url     : https://prove2.me/theorems/b04cd591-de86-44aa-895f-df2aacff891c
-- title:
--   Pad injective
-- statement:
--   Formal statement of `ImmuneSystem.PAst.pad_injective` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ImmuneSystem.PAst.pad_injective: Function.Injective pad := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneSemantics.lean#L165

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

theorem ImmuneSystem.PAst.pad_injective: Function.Injective pad := by sorry
