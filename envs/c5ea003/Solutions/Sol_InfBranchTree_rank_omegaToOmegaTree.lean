-- Prove2me | solution 1 for InfBranchTree.rank_omegaToOmegaTree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:29:58.630594+00:00
-- url     : https://prove2.me/submissions/1136fa8d-f5d4-46a0-bef7-e24d86967ae1

-- Sol generated from MachineLearning/CNFRealizability.lean
import Mathlib
import Definitions.Def_MachineLearning_CNFRealizability
import Theorems.Thm_InfBranchTree_iSup_omega0_pow_nat
import Theorems.Thm_InfBranchTree_rank_omegaPowTree

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
    rank omegaToOmegaTree = omega0 ^ omega0 := by
      convert iSup_omega0_pow_nat using 1;
      refine' le_antisymm _ _;
      · refine' Ordinal.iSup_le _;
        intro n; rw [ rank_omegaPowTree ] ; exact le_trans ( by aesop ) ( le_ciSup ( Ordinal.bddAbove_of_small ) ( n + 1 ) ) ;
      · refine' ciSup_le fun n => _;
        refine' le_trans _ ( le_ciSup _ n );
        · rw [ rank_omegaPowTree ];
          exact le_of_lt ( Order.lt_succ _ );
        · refine' ⟨ omega0 ^ omega0 + 1, Set.forall_mem_range.2 fun i => _ ⟩;
          refine' le_trans ( Order.succ_le_of_lt _ ) ( le_add_of_nonneg_right zero_le_one );
          rw [ rank_omegaPowTree ];
          exact_mod_cast Ordinal.opow_lt_opow_iff_right ( by norm_num ) |>.2 ( Ordinal.nat_lt_omega0 i )
