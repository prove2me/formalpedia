-- Prove2me | Definitions.Def_Bridges_UltrametricProofCodeDuality
-- name    : Bridges_UltrametricProofCodeDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:59.167884+00:00
-- url     : https://prove2.me/theorems/8072fe68-700b-49e1-8d80-e0bb5caa68ac
-- title:
--   Aether Catalog definitions — Bridges_UltrametricProofCodeDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricProofCodeDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricProofCodeDuality.lean by skeleton subtraction
import Mathlib
/-
# Ultrametric Proof-Code Duality

This file establishes a formal algebraic dictionary between three domains:
1. **Prime-congruence algebra** on finite observer families
2. **Finite ultrametric geometry** and dendrogram reconstruction
3. **Certified hierarchical decoding** with cryptographic semantics

## Main Results

### Core Definitions
* `kernelAtLevel` — equivalence relation induced by observers up to a given level
* `NatUltrametric` — ℕ-valued ultrametric structure
* `ObsKernel` — kernel of a subfamily of observers
* `NestedPartitionSystem` — certified hierarchical partition
* `sepLevelBounded` — separation level between points

### Theorems
* `kernelAtLevel_refl/symm/trans` — observer kernels are equivalence relations
* `kernelAtLevel_antitone` — higher levels yield finer kernels
* `closedBall_eq_kernelClass` — closed balls are exactly observer kernel classes
* `ultrametric_isosceles` — all ultrametric triangles are isosceles
* `canonical_observers_separate` — canonical observers separate points
* `canonical_full_separation` — full characterization of separation
* `reconstruction_correct` — round-trip correctness
* `sepLevelBounded_ultrametric` — separation levels satisfy ultrametric inequality
* `binaryTree_*` — concrete verified example on a 4-point ultrametric
-/


set_option maxHeartbeats 800000

open Finset Function

noncomputable section

/-! ## §1. Observer Kernels and Level Filtrations -/

/-- The kernel at level `k`: `x` and `y` are indistinguishable by all
    observers whose level is at most `k`. -/
def kernelAtLevel {P ι S : Type*} (O : ι → P → S) (lvl : ι → ℕ)
    (k : ℕ) (x y : P) : Prop :=
  ∀ i : ι, lvl i ≤ k → O i x = O i y

/-- The observer kernel of a set of indices `J`. -/
def ObsKernel {P ι S : Type*} (O : ι → P → S) (J : Finset ι) : Set (P × P) :=
  {p | ∀ j ∈ J, O j p.1 = O j p.2}

/-! ## §2. Kernel Equivalence Relations -/






/-! ## §3. ℕ-Valued Ultrametric -/

/-- An ultrametric on a type using ℕ-valued distances. -/
structure NatUltrametric (P : Type*) where
  d : P → P → ℕ
  d_self : ∀ x, d x x = 0
  d_symm : ∀ x y, d x y = d y x
  d_pos : ∀ x y, d x y = 0 → x = y
  d_ultra : ∀ x y z, d x z ≤ max (d x y) (d y z)


/-! ## §4. Closed Balls -/

/-- Closed ball of radius `k` in a NatUltrametric. -/
def NatUltrametric.closedBall {P : Type*} (U : NatUltrametric P) (x : P) (k : ℕ) : Set P :=
  {y | U.d x y ≤ k}



/-! ## §5. Ball-Kernel Duality -/


/-! ## §6. Ultrametric Isosceles Theorem -/

/-
**Ultrametric isosceles theorem**: In any `NatUltrametric`, if `d(x,y) ≠ d(y,z)`,
    then `d(x,z) = max(d(x,y), d(y,z))`.
-/

/-! ## §7. Observer Kernel Lattice -/




/-! ## §8. Nested Partition Systems and Reconstruction -/

/-- A nested partition system: equivalence relations at each level, with nesting. -/
structure NestedPartitionSystem (P : Type*) where
  rel : ℕ → P → P → Prop
  refl_rel : ∀ k x, rel k x x
  symm_rel : ∀ k x y, rel k x y → rel k y x
  trans_rel : ∀ k x y z, rel k x y → rel k y z → rel k x z
  nested : ∀ k l x y, k ≤ l → rel k x y → rel l x y

/-- Construct the canonical nested partition system from a `NatUltrametric`. -/
def canonicalNPS {P : Type*} (U : NatUltrametric P) : NestedPartitionSystem P where
  rel k x y := U.d x y ≤ k
  refl_rel k x := by simp [U.d_self]
  symm_rel k x y h := by rwa [U.d_symm]
  trans_rel k x y z hxy hyz := le_trans (U.d_ultra x y z) (max_le hxy hyz)
  nested _ _ _ _ hkl hxy := le_trans hxy hkl


/-! ## §9. Canonical Observers and Separation -/

/-- Canonical observer family: observer `i` maps `p` to `d(i, p)`. -/
def canonicalObserver {P : Type*} (U : NatUltrametric P) : P → P → ℕ :=
  fun i p => U.d i p




/-! ## §10. Decoding Duality -/


/-! ## §11. Kernel Refinement Chain -/


/-! ## §12. Separation Level and Ultrametric Inequality -/

/-- Separation level: the minimum level of any observer that distinguishes `x` from `y`.
    Returns 0 if no observer distinguishes them. -/
def sepLevelBounded {P ι S : Type*} [DecidableEq S] [Fintype ι]
    (O : ι → P → S) (lvl : ι → ℕ) (x y : P) : ℕ :=
  if h : ∃ i : ι, O i x ≠ O i y then
    (Finset.univ.filter (fun i => O i x ≠ O i y)).image (fun i => lvl i)
      |>.min' (by
        rw [Finset.image_nonempty, Finset.filter_nonempty_iff]
        exact h.imp (fun i hi => ⟨Finset.mem_univ i, hi⟩))
  else 0



/-
Helper: sepLevelBounded is ≤ lvl j for any distinguishing observer j.
-/


/-- **Observer-induced distance**: the maximum level of any distinguishing observer.
    Higher values mean more separated. Returns 0 for indistinguishable points. -/
def obsDist {P ι S : Type*} [DecidableEq S] [Fintype ι]
    (O : ι → P → S) (lvl : ι → ℕ) (x y : P) : ℕ :=
  if h : ∃ i : ι, O i x ≠ O i y then
    (Finset.univ.filter (fun i => O i x ≠ O i y)).image (fun i => lvl i)
      |>.max' (by
        rw [Finset.image_nonempty, Finset.filter_nonempty_iff]
        exact h.imp (fun i hi => ⟨Finset.mem_univ i, hi⟩))
  else 0



/-
Helper: obsDist is ≥ lvl j for any distinguishing observer j.
-/

/-
**Ultrametric inequality for observer distance**:
    `obsDist(x,z) ≤ max(obsDist(x,y), obsDist(y,z))`.

    Any observer distinguishing `x` from `z` must also distinguish either
    `x` from `y` or `y` from `z`, so its level contributes to one of the
    right-hand side maxima.
-/

/-! ## §13. Concrete Example: Binary Tree Ultrametric -/

/-- A 4-point ultrametric: d(0,1) = 1, d(2,3) = 1, cross-distance = 2. -/
def binaryTreeDist : Fin 4 → Fin 4 → ℕ
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 0
  | ⟨2, _⟩, ⟨2, _⟩ => 0
  | ⟨2, _⟩, ⟨3, _⟩ => 1
  | ⟨3, _⟩, ⟨2, _⟩ => 1
  | ⟨3, _⟩, ⟨3, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 2
  | ⟨0, _⟩, ⟨3, _⟩ => 2
  | ⟨1, _⟩, ⟨2, _⟩ => 2
  | ⟨1, _⟩, ⟨3, _⟩ => 2
  | ⟨2, _⟩, ⟨0, _⟩ => 2
  | ⟨2, _⟩, ⟨1, _⟩ => 2
  | ⟨3, _⟩, ⟨0, _⟩ => 2
  | ⟨3, _⟩, ⟨1, _⟩ => 2
  | ⟨n + 4, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 4, h⟩ => absurd h (by omega)

theorem binaryTreeDist_self (x : Fin 4) : binaryTreeDist x x = 0 := by
  fin_cases x <;> rfl

theorem binaryTreeDist_symm (x y : Fin 4) : binaryTreeDist x y = binaryTreeDist y x := by
  fin_cases x <;> fin_cases y <;> rfl

theorem binaryTreeDist_pos (x y : Fin 4) (h : binaryTreeDist x y = 0) : x = y := by
  fin_cases x <;> fin_cases y <;> simp_all [binaryTreeDist]

theorem binaryTreeDist_ultra (x y z : Fin 4) :
    binaryTreeDist x z ≤ max (binaryTreeDist x y) (binaryTreeDist y z) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [binaryTreeDist]

/-- The binary tree distance forms a valid NatUltrametric. -/
def binaryTreeUltrametric : NatUltrametric (Fin 4) where
  d := binaryTreeDist
  d_self := binaryTreeDist_self
  d_symm := binaryTreeDist_symm
  d_pos := binaryTreeDist_pos
  d_ultra := binaryTreeDist_ultra





/-- Observer family for the binary tree: two observers. -/
def binaryTreeObserver : Fin 2 → Fin 4 → Fin 2
  | ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨0, _⟩, ⟨3, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => 0
  | ⟨1, _⟩, ⟨3, _⟩ => 1
  | ⟨n + 2, h⟩, _ => absurd h (by omega)
  | _, ⟨n + 4, h⟩ => absurd h (by omega)



end


