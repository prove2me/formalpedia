-- Prove2me | solution 1 for InfBranchTree.rank_omegaPowTree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:28:31.753692+00:00
-- url     : https://prove2.me/submissions/b387ea5e-f39f-466e-a2cb-99b377fe8c12

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


private theorem succ_add_eq_add_succ (a b : Ordinal) :
    Order.succ (a + b) = a + Order.succ b := by
      rw [ Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc ]

private theorem add_iSup_eq (a : Ordinal) (f : ℕ → Ordinal) :
    a + ⨆ i, f i = ⨆ i, (a + f i) := by
      convert Ordinal.IsNormal.map_iSup ( isNormal_add_right a ) ?_ using 1;
      · infer_instance;
      · exact ⟨ 0 ⟩

/-- **Rank Addition Theorem**: Prepending realizes ordinal addition on ranks.
The key identity is `rank (prepend s t) = rank s + rank t`. -/
theorem rank_prepend (s t : InfBranchTree) :
    rank (prepend s t) = rank s + rank t := by
  induction t with
  | leaf => simp [prepend, rank, add_zero]
  | node f ih =>
    simp only [prepend, rank]
    conv_lhs => arg 1; ext i; rw [ih i]
    simp_rw [succ_add_eq_add_succ]
    rw [add_iSup_eq]


/-
**Rank Multiplication Theorem**: `mulByNat` realizes ordinal multiplication by ℕ.
-/
theorem rank_mulByNat (t : InfBranchTree) (k : ℕ) :
    rank (mulByNat t k) = rank t * (k : Ordinal) := by
      induction' k with k ih;
      · aesop;
      · convert rank_prepend t ( t.mulByNat k ) using 1;
        rw [ ih, Nat.cast_succ, mul_add, mul_one ];
        induction' k with k ih;
        · norm_num;
        · induction' k + 1 with k ih <;> simp_all +decide [ Nat.cast_succ, mul_add, add_assoc ];

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
theorem solution(n : ℕ) :
    rank (omegaPowTree n) = omega0 ^ (n : Ordinal) := by
      induction n <;> simp_all +decide [ pow_succ, omegaPowTree ];
      · simp +decide [ InfBranchTree.rank ];
      · rw [ show ( node fun k => ( omegaPowTree _ ).mulByNat k ).rank = ⨆ k : ℕ, Order.succ ( ( omegaPowTree _ ).mulByNat k ).rank from rfl ];
        simp_all +decide [ rank_mulByNat ];
        rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · simp +decide [ mul_add ];
        · intro w hw;
          contrapose! hw;
          rw [ Ordinal.mul_le_iff_of_isSuccLimit ];
          · intro b' hb';
            rcases Ordinal.lt_omega0.1 hb' with ⟨ k, rfl ⟩;
            exact le_trans ( Order.le_succ _ ) ( hw k );
          · exact Ordinal.isSuccLimit_omega0
