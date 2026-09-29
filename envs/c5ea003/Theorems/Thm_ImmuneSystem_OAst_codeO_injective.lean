-- Prove2me | Theorems.Thm_ImmuneSystem_OAst_codeO_injective
-- name    : ImmuneSystem.OAst.codeO_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:42:27.908985+00:00
-- url     : https://prove2.me/theorems/d11f25b5-e9b7-4ff4-b67a-7a3c5d3b2a31
-- title:
--   CodeO injective
-- statement:
--   Formal statement of `ImmuneSystem.OAst.codeO_injective` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ImmuneSystem.OAst.codeO_injective: Function.Injective codeO := by sorry
--   variable (O : ℕ → ℕ)
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ImmuneOracle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ImmuneOracle.lean#L57

-- Thm stub generated from Shared/ImmuneOracle.lean
import Mathlib
import Definitions.Def_Shared_ImmuneOracle
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

open ImmuneSystem


open OAst

theorem ImmuneSystem.OAst.codeO_injective: Function.Injective codeO := by sorry
