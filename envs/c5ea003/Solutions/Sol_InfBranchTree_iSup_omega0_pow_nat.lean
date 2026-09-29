-- Prove2me | solution 1 for InfBranchTree.iSup_omega0_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:28:31.195619+00:00
-- url     : https://prove2.me/submissions/50a08aee-bd36-4f39-ac76-3329c064e617

-- Sol generated from MachineLearning/CNFRealizability.lean
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

/-
**ω^ω Realization Theorem**: `omegaToOmegaTree` has rank exactly `ω^ω`.
This is the first true limit-stage synthesis theorem: the tree formalism
can encode transfinite convergence of structural complexity.
-/

/-! ## Corollaries -/





open InfBranchTree in
theorem solution:
    ⨆ n : ℕ, omega0 ^ (n : Ordinal) = omega0 ^ omega0 := by
      convert ( Ordinal.IsNormal.map_iSup _ _ );
      convert rfl;
      rotate_left;
      convert ( Ordinal.IsNormal.map_iSup _ _ );
      convert rfl;
      convert Ordinal.iSup_natCast;
      all_goals try infer_instance;
      · exact Ordinal.isNormal_opow one_lt_omega0;
      · exact Ordinal.isNormal_opow ( by simp +decide );
      · convert ( Ordinal.IsNormal.map_iSup _ _ );
        · exact Ordinal.isNormal_opow one_lt_omega0;
        · infer_instance;
        · exact ⟨ 0 ⟩
