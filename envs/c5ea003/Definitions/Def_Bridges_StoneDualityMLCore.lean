-- Prove2me | Definitions.Def_Bridges_StoneDualityMLCore
-- name    : Bridges_StoneDualityMLCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:27:40.913257+00:00
-- url     : https://prove2.me/theorems/4c7586d5-00f2-44e5-848b-d0c6695bf5ad
-- title:
--   Aether Catalog definitions — Bridges_StoneDualityMLCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.StoneDualityMLCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/StoneDualityMLCore.lean by skeleton subtraction
import Mathlib
/-
# Stone Duality for Machine Learning: Boolean Hypothesis Algebras and
  Topological Online Learnability Certification

Bridge: connects Algebra (Boolean algebras, Stone spaces) to Machine Learning
(online learnability, Littlestone dimension, mistake bounds) via Topology
(Cantor-Bendixson rank, compact zero-dimensional spaces).
-/


open Set Function Finset

namespace StoneDualityML

/-! ## Section 1: Hypothesis Classes and Growth Functions
Bridge: Machine Learning ↔ Combinatorics -/

/-- A hypothesis class over Fin n.
    Bridge: ML (hypothesis classes) ↔ Algebra (Boolean structure). -/
structure FinHypClass (n : ℕ) where
  hyps : Finset (Fin n → Bool)
  nonempty : hyps.Nonempty

/-- The growth function: distinct labelings on S.
    Bridge: ML (VC theory) ↔ Combinatorics (Sauer-Shelah) -/
noncomputable def growthFn {n : ℕ} (H : FinHypClass n) (S : Finset (Fin n)) : ℕ :=
  (H.hyps.image (fun h => fun x : S => h x)).card


/-! ## Section 2: Cantor-Bendixson Derivative Theory
Bridge: Topology ↔ Descriptive Set Theory -/

/-- Accumulation point of set A.
    Bridge: Topology ↔ Descriptive Set Theory -/
def IsAccPt' {X : Type*} [TopologicalSpace X] (x : X) (A : Set X) : Prop :=
  x ∈ A ∧ ∀ U : Set X, IsOpen U → x ∈ U → ∃ y ∈ A, y ≠ x ∧ y ∈ U

/-- The Cantor-Bendixson derivative: accumulation points of A.
    Bridge: Topology ↔ Descriptive Set Theory -/
def cbDeriv {X : Type*} [TopologicalSpace X] (A : Set X) : Set X :=
  {x | IsAccPt' x A}

/-- Iterated CB derivative. -/
def cbIter {X : Type*} [TopologicalSpace X] : ℕ → Set X → Set X
  | 0, A => A
  | n + 1, A => cbDeriv (cbIter n A)

/-- Isolated point in a set. -/
def IsIsolatedIn' {X : Type*} [TopologicalSpace X] (x : X) (A : Set X) : Prop :=
  x ∈ A ∧ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ A ∩ U = {x}

/-- Perfect kernel: ⋂ₙ cbIter n A. -/
def perfKernel {X : Type*} [TopologicalSpace X] (A : Set X) : Set X :=
  ⋂ n, cbIter n A













/-! ## Section 3: Binary Trees and Shattering
Bridge: ML (online learning) ↔ Combinatorics -/

/-- Complete binary tree of depth d with ℕ labels at internal nodes. -/
inductive STree : ℕ → Type where
  | leaf : STree 0
  | node : {d : ℕ} → ℕ → STree d → STree d → STree (d + 1)

/-- Number of leaves. -/
def STree.numLeaves : {d : ℕ} → STree d → ℕ
  | _, .leaf => 1
  | _, .node _ l r => l.numLeaves + r.numLeaves


/-- Number of internal nodes. -/
def STree.numNodes : {d : ℕ} → STree d → ℕ
  | _, .leaf => 0
  | _, .node _ l r => 1 + l.numNodes + r.numNodes


/-- Shattering of a tree by hypotheses.
    Bridge: ML ↔ Combinatorics -/
def Shatters (S : Finset (ℕ → Bool)) : {d : ℕ} → STree d → Prop
  | _, .leaf => True
  | _, .node x l r =>
    (∃ h ∈ S, h x = true) ∧ (∃ h ∈ S, h x = false) ∧
    Shatters (S.filter (· x = true)) l ∧
    Shatters (S.filter (· x = false)) r



/-! ## Section 4: Cylinder Sets
Bridge: Algebra ↔ Topology ↔ ML -/

/-- Cylinder set: hypotheses with h(x) = b.
    Bridge: Topology (clopen) ↔ Algebra (Boolean generators) -/
def cylSet {α : Type*} (x : α) (b : Bool) : Set (α → Bool) := {h | h x = b}




/-! ## Section 5: Hamming Metric
Bridge: Analysis ↔ ML (certified robustness) -/

/-- Hamming distance on Bool^n.
    Bridge: ML (similarity) ↔ Analysis (metrics) -/
def hammingDist (n : ℕ) (h₁ h₂ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun x => h₁ x ≠ h₂ x)).card





/-! ## Section 6: Exponential Bounds
Bridge: ML ↔ Cryptography ↔ Information Theory -/





/-! ## Section 7: Perfect Set Theory
Bridge: Topology ↔ ML -/



/-! ## Section 8: Summary Bridge Theorems -/





end StoneDualityML


