-- Prove2me | Theorems.Thm_InfBranchTree_iSup_omega0_pow_nat
-- name    : InfBranchTree.iSup_omega0_pow_nat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:53.934153+00:00
-- url     : https://prove2.me/theorems/550931e5-eeaa-4a08-8eed-fe6efd3af532
-- title:
--   ISup omega0 pow nat
-- statement:
--   Formal statement of `InfBranchTree.iSup_omega0_pow_nat` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem InfBranchTree.iSup_omega0_pow_nat:
--       ⨆ n : ℕ, omega0 ^ (n : Ordinal) = omega0 ^ omega0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CNFRealizability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CNFRealizability.lean#L178

-- Thm stub generated from MachineLearning/CNFRealizability.lean
import Mathlib
import Definitions.Def_MachineLearning_CNFRealizability

/-!
# Cantor Normal Form Realizability and ω^ω Realization

This module extends the ordinal collapse theory to prove that `InfBranchTree`
provides a **complete constructive semantics for all ordinals below ω^ω** via
Cantor normal form, and constructs a tree realizing `ω^ω` itself.

## Main Definitions

* `InfBranchTree.prepend` — Tree composition yielding ordinal addition on ranks.
* `InfBranchTree.mulByNat` — Tree repetition yielding ordinal multiplication by ℕ.
* `InfBranchTree.omegaPowTree` — Canonical tree of rank `ω^n`.
* `InfBranchTree.cnfTree` — Tree built from a CNF coefficient/exponent list.
* `InfBranchTree.omegaToOmegaTree` — Canonical tree of rank `ω^ω`.

## Main Results

### Cluster E: Tree Algebra Operations
* `rank_prepend` — `rank (prepend s t) = rank s + rank t`
* `rank_mulByNat` — `rank (mulByNat t k) = rank t * k`

### Cluster F: Ordinal Power Realization
* `rank_omegaPowTree` — `rank (omegaPowTree n) = ω^n`

### Cluster G: Cantor Normal Form Realizability
* `rank_cnfTree` — CNF lists are exactly realized by `cnfTree`.

### Cluster H: ω^ω Realization
* `rank_omegaToOmegaTree` — `rank omegaToOmegaTree = ω^ω`
-/

noncomputable section

open Ordinal

/-! ## InfBranchTree (reproduced from Basic) -/


open InfBranchTree


/-! ## Cluster E: Tree Algebra Operations -/






/-
**Rank Multiplication Theorem**: `mulByNat` realizes ordinal multiplication by ℕ.
-/

/-! ## Cluster F: Ordinal Power Realization -/


/-
**Ordinal Power Realization**: `omegaPowTree n` has rank exactly `ω^n`.
-/

/-! ## Cluster G: Cantor Normal Form Realizability -/






/-
**CNF Realizability Theorem**: The rank of `cnfTree L` equals the
CNF ordinal value `cnfValue L`. This holds for all lists, not just valid CNFs.
-/

/-! ## Cluster H: ω^ω Realization -/


/-
Auxiliary: `⨆ n : ℕ, ω^n = ω^ω`
-/

theorem InfBranchTree.iSup_omega0_pow_nat:
    ⨆ n : ℕ, omega0 ^ (n : Ordinal) = omega0 ^ omega0 := by sorry
