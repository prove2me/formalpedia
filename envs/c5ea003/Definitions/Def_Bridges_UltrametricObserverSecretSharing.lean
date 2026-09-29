-- Prove2me | Definitions.Def_Bridges_UltrametricObserverSecretSharing
-- name    : Bridges_UltrametricObserverSecretSharing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:35.130988+00:00
-- url     : https://prove2.me/theorems/7fbc7e2f-260d-4450-af7a-675caad00892
-- title:
--   Aether Catalog definitions — Bridges_UltrametricObserverSecretSharing
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricObserverSecretSharing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricObserverSecretSharing.lean by skeleton subtraction
import Mathlib
/-
# Ultrametric Observer Secret Sharing

This file formalizes a bridge between **observer families on proof states**,
**ultrametric geometry**, and **threshold reconstruction** (secret sharing).

## Main Results

* `observerDistFromVal_pseudoultrametric` — observer disagreement count induces
  an ultrametric pseudodistance
* `ultrametric_balls_laminar` — closed balls in any ultrametric are laminar
* `reconstruction_iff_separating` — reconstruction ↔ separation on the observer subset
* `minimal_reconstruction_witness` — each observer in a minimal set has a unique witness pair
* `compatible_compression_nonexpanding` — observer-compatible compression is nonexpanding
* `compression_preserves_reconstruction` — compression preserves reconstructibility
* `observer_equiv_refinement` — finer radius gives finer equivalence classes
* `exists_observer_valuation_ultrametric` — main bridge theorem combining all results
-/


set_option maxHeartbeats 800000

open Function Finset

noncomputable section

/-! ## §1. Observer Families -/

/-- An observer family: n observation functions from states α to observations β. -/
structure ObserverFamily (α β : Type*) (n : ℕ) where
  observe : Fin n → α → β

/-- Two states are fully code-equivalent if ALL observers agree on them. -/
def CodeEquiv {α β : Type*} {n : ℕ} (F : ObserverFamily α β n) (x y : α) : Prop :=
  ∀ i : Fin n, F.observe i x = F.observe i y

/-- An observer family is separating on a set S if for every distinct pair,
    at least one observer distinguishes them. -/
def IsSeparating {α β : Type*} [DecidableEq α] {n : ℕ}
    (F : ObserverFamily α β n) (S : Finset α) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i : Fin n, F.observe i x ≠ F.observe i y


/-! ## §2. Observer-Induced Distance -/

/-- The observer agreement count: number of observers that agree on (x,y). -/
def obsAgreeCount {α β : Type*} [DecidableEq β] {n : ℕ}
    (F : ObserverFamily α β n) (x y : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => F.observe i x = F.observe i y)).card

/-- The observer disagreement count: n minus the agreement count.
    This serves as the observer-induced distance. -/
def observerDistFromVal {α β : Type*} [DecidableEq β] {n : ℕ}
    (F : ObserverFamily α β n) (x y : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => F.observe i x ≠ F.observe i y)).card

/-
Agreement + disagreement = n.
-/

/-
The observer distance is symmetric.
-/

/-
Self-distance is zero.
-/

/-
Zero distance implies code equivalence.
-/

/-
The observer distance satisfies d(x,z) ≤ d(x,y) + d(y,z).
    Proof: if observer i distinguishes x from z, then either it distinguishes
    x from y or y from z (by transitivity of equality).
-/

/-! ## §3. Ultrametric Ball Structure -/

/-- An ultrametric pseudometric on ℕ values. -/
structure IsNatUltraPseudometric {α : Type*} (d : α → α → ℕ) : Prop where
  self_zero : ∀ x, d x x = 0
  symm : ∀ x y, d x y = d y x
  strong_triangle : ∀ x y z, d x z ≤ max (d x y) (d y z)

/-- A closed ball in a ℕ-valued distance space. -/
def closedBall' {α : Type*} (d : α → α → ℕ) (x : α) (r : ℕ) : Set α :=
  {y | d x y ≤ r}


/-
**Key lemma**: In an ultrametric space, every point of a ball is a center.
    If d(x,y) ≤ r, then B_r(x) = B_r(y).
-/

/-
**Main Theorem: Ultrametric balls are laminar.**
    For any ultrametric pseudodistance, any two closed balls are either
    disjoint or one contains the other.
-/

/-! ## §4. Reconstruction -/

/-- T reconstructs x from S if T-restricted observers separate x from all other S-elements. -/
def Reconstructs {α β : Type*} [DecidableEq β] [DecidableEq α] {n : ℕ}
    (F : ObserverFamily α β n) (S : Finset α) (T : Finset (Fin n)) (x : α) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, x ≠ y → ∃ i ∈ T, F.observe i x ≠ F.observe i y

/-- T fully reconstructs S if it reconstructs every element. -/
def FullyReconstructs {α β : Type*} [DecidableEq β] [DecidableEq α] {n : ℕ}
    (F : ObserverFamily α β n) (S : Finset α) (T : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, Reconstructs F S T x

/-- T is a minimal reconstruction subset for S. -/
def MinimalReconstruction {α β : Type*} [DecidableEq β] [DecidableEq α] {n : ℕ}
    (F : ObserverFamily α β n) (S : Finset α) (T : Finset (Fin n)) : Prop :=
  FullyReconstructs F S T ∧ ∀ T' ⊂ T, ¬FullyReconstructs F S T'

/-
**Theorem C: Reconstruction ↔ Separation.**
    T fully reconstructs S iff T-restricted observers separate all distinct pairs.
-/

/-
**Theorem D: Minimal Reconstruction Witness.**
    In a minimal reconstruction subset, each observer has a unique "witness pair":
    a pair of states that only this observer from T separates.
-/

/-! ## §5. Compression -/

/-- A compression operator on states. -/
structure CompressionOp (α : Type*) where
  compress : α → α

/-- A compression is observer-compatible if it commutes with all observers. -/
def IsObserverCompatible {α β : Type*} {n : ℕ}
    (F : ObserverFamily α β n) (comp : CompressionOp α) : Prop :=
  ∀ i : Fin n, ∀ x : α, F.observe i (comp.compress x) = F.observe i x

/-- Nonexpanding: compression never increases distance. -/
def IsNonexpanding {α : Type*} (comp : CompressionOp α) (d : α → α → ℕ) : Prop :=
  ∀ x y, d (comp.compress x) (comp.compress y) ≤ d x y

/-
**Theorem E-1: Compatible compression is nonexpanding.**
-/

/-
**Theorem E-2: Compatible compression preserves reconstruction.**
-/

/-! ## §6. Equivalence Refinement -/

/-- The observer equivalence at radius r: x ~ y iff they agree on at least (n - r) observers. -/
def observerEquivAtRadius {α β : Type*} [DecidableEq β] {n : ℕ}
    (F : ObserverFamily α β n) (r : ℕ) (x y : α) : Prop :=
  observerDistFromVal F x y ≤ r

/-
**Theorem B: Equivalence Refinement.**
    Finer radius gives finer equivalence classes.
-/

/-! ## §7. Main Bridge Theorem -/

/-
**Theorem A: Observer Valuation Ultrametric (Main Bridge).**
    For a separating observer family:
    1. The observer distance is an ultrametric pseudometric.
    2. On the separated set, zero distance implies equality.
    3. Closed balls are laminar.
-/

end


