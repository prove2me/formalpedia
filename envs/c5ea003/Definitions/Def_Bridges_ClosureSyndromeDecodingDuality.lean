-- Prove2me | Definitions.Def_Bridges_ClosureSyndromeDecodingDuality
-- name    : Bridges_ClosureSyndromeDecodingDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:56.267748+00:00
-- url     : https://prove2.me/theorems/ce70aa38-5b66-44d3-bd04-8a43e55a2527
-- title:
--   Aether Catalog definitions — Bridges_ClosureSyndromeDecodingDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureSyndromeDecodingDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureSyndromeDecodingDuality.lean by skeleton subtraction
import Mathlib

/-!
# Closure–Syndrome Decoding Duality via Idempotent Parity Semimodules
# and Certified Minimal Tanner Reconstruction

This file formalizes a finite duality theorem that connects closure-theoretic parity
data to canonical decoding objects. The core insight is:

> **Syndrome geometry is latent in finite closure systems, and idempotent semimodule
> structure provides the algebraic language for extracting unique minimal
> Tanner-style realizations.**

## Main Structures

* `FinClosureOp` — Finite closure operator on `Finset α`
* `ClosureParitySystem` — Closure operator with parity observables (supports + weights)
* `TannerHypergraph` — Bipartite incidence structure (variable nodes ↔ check nodes)

## Main Theorems

* `canonical_tanner_realizes` — The canonical Tanner hypergraph realizes the parity system
* `minimal_checkNodes_eq_activeObs` — Minimal realizations use exactly the active observables
* `canonical_tanner_minimal` — The canonical construction achieves minimum check count
* `minimal_realization_equiv` — Uniqueness: any two minimal realizations agree
* `syndrome_eq_tanner_sum` — Syndrome computation factors through the Tanner structure
* `syndrome_separates_of_support_disjoint` — Support disjointness implies syndrome separation
* `parity_indicator_support_recovers` — Support sets are recoverable from indicator vectors
* `certified_minimal_tanner_reconstruction` — Main duality package: existence, minimality,
  syndrome factorization, and uniqueness of minimal Tanner realization

## Cross-Domain Connections

- **Algebra ↔ Coding Theory**: Closure-parity systems ↔ sparse parity-check structures
- **Tropical Geometry ↔ Decoding**: Parity indicator vectors ↔ tropical semimodule generators
- **Cryptography ↔ Closure Capacity**: Tanner reconstruction ↔ certified code design
- **Information Theory ↔ Syndrome Geometry**: Syndrome separation ↔ support separation
-/

set_option maxHeartbeats 400000

open Finset Function

noncomputable section

namespace ClosureSyndromeDecoding

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## §1. Finite Closure Operators -/

/-- A finite closure operator on `Finset α`: extensive, monotone, idempotent. -/
structure FinClosureOp (α : Type*) [Fintype α] [DecidableEq α] where
  /-- The closure map -/
  cl : Finset α → Finset α
  /-- Extensivity: every set is contained in its closure -/
  extensive : ∀ s : Finset α, s ⊆ cl s
  /-- Monotonicity: larger sets have larger closures -/
  mono : ∀ ⦃s t : Finset α⦄, s ⊆ t → cl s ⊆ cl t
  /-- Idempotency: closing twice is the same as closing once -/
  idem : ∀ s : Finset α, cl (cl s) = cl s

namespace FinClosureOp

variable {α : Type*} [Fintype α] [DecidableEq α] (C : FinClosureOp α)

/-- A set is closed if it equals its own closure. -/
def IsClosed (s : Finset α) : Prop := C.cl s = s

instance decidableIsClosed : DecidablePred C.IsClosed :=
  fun s => decEq (C.cl s) s




end FinClosureOp

/-! ## §2. Closure-Parity Systems -/

/-- A closure-parity system on finite types `α` (symbols) and `Obs` (observables).
    Each observable has a support set (which must be closed) and a weight. -/
structure ClosureParitySystem (α Obs : Type*)
    [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs] where
  /-- The underlying closure operator -/
  cl : FinClosureOp α
  /-- Support set of each observable (a closed set of symbols) -/
  supp : Obs → Finset α
  /-- Weight/cost assigned to each observable -/
  wt : Obs → ℕ
  /-- Each support set is closed under the closure operator -/
  supp_closed : ∀ o, cl.IsClosed (supp o)

namespace ClosureParitySystem

variable {α Obs : Type*} [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs]

/-- The set of observables with nonempty support — the "active" checks. -/
def activeObs (sys : ClosureParitySystem α Obs) : Finset Obs :=
  Finset.univ.filter (fun o => sys.supp o ≠ ∅)


/-- Separation condition: distinct observables have distinct supports.
    This is the nondegeneracy condition ensuring unique reconstruction. -/
def Separated (sys : ClosureParitySystem α Obs) : Prop :=
  Function.Injective sys.supp



end ClosureParitySystem

/-! ## §3. Tanner Hypergraphs -/

/-- A Tanner hypergraph: a bipartite incidence structure between variable nodes
    (elements of `α`) and check nodes (a subset of `Obs`).
    Each check node has an associated support (hyperedge) and weight. -/
structure TannerHypergraph (α Obs : Type*)
    [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs] where
  /-- The active check nodes -/
  checkNodes : Finset Obs
  /-- Incidence: the support/hyperedge of each check node -/
  incidence : Obs → Finset α
  /-- Weight assigned to each check node -/
  checkWeight : Obs → ℕ

namespace TannerHypergraph

variable {α Obs : Type*} [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs]

/-- A Tanner hypergraph **realizes** a closure-parity system if:
    1. Every observable with nonempty support appears as a check node
    2. Check node supports match the system's supports
    3. Check node weights match the system's weights -/
def Realizes (T : TannerHypergraph α Obs) (sys : ClosureParitySystem α Obs) : Prop :=
  (∀ o, sys.supp o ≠ ∅ → o ∈ T.checkNodes) ∧
  (∀ o ∈ T.checkNodes, T.incidence o = sys.supp o) ∧
  (∀ o ∈ T.checkNodes, T.checkWeight o = sys.wt o)

/-- A realization is **minimal** if it has the fewest check nodes among all realizations. -/
def IsMinimalRealization (T : TannerHypergraph α Obs)
    (sys : ClosureParitySystem α Obs) : Prop :=
  T.Realizes sys ∧
  ∀ T' : TannerHypergraph α Obs, T'.Realizes sys → T.checkNodes.card ≤ T'.checkNodes.card

/-- Two Tanner hypergraphs are **equivalent** if they agree on check nodes,
    incidence, and weights restricted to active checks. -/
def Equiv (T₁ T₂ : TannerHypergraph α Obs) : Prop :=
  T₁.checkNodes = T₂.checkNodes ∧
  (∀ o ∈ T₁.checkNodes, T₁.incidence o = T₂.incidence o) ∧
  (∀ o ∈ T₁.checkNodes, T₁.checkWeight o = T₂.checkWeight o)


end TannerHypergraph

/-! ## §4. Canonical Tanner Construction -/

/-- The **canonical Tanner hypergraph**: uses exactly the active observables as
    check nodes, with supports and weights inherited from the parity system. -/
def canonicalTanner {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) : TannerHypergraph α Obs where
  checkNodes := sys.activeObs
  incidence := sys.supp
  checkWeight := sys.wt

/-! ## §5. Realization and Minimality Theorems -/


/-
In any minimal realization, the check nodes are exactly the active observables.
    This is the key structural lemma for uniqueness.
-/

/-
The canonical Tanner hypergraph is a minimal realization.
-/

/-
**Uniqueness**: any two minimal realizations of a closure-parity system
    are equivalent (same check nodes, same incidence, same weights).
-/

/-! ## §6. Syndrome Map -/

/-- The **syndrome** of a word `w : α → ℕ` at observable `o` is the sum of `w`
    over the support of `o`. This captures parity-check evaluation. -/
def syndrome {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (w : α → ℕ) (o : Obs) : ℕ :=
  (sys.supp o).sum w




/-! ## §7. Syndrome Separation -/

/-
If two observables have disjoint supports, the indicator function of one's
    support produces different syndromes at the two observables (provided both
    supports are nonempty). This is syndrome separation from support geometry.
-/

/-
Under separation, distinct active observables are distinguished by some syndrome.
-/

/-! ## §8. Parity Indicator Vectors (Tropical Semimodule Generators) -/

/-- The **parity indicator** vector for observable `o`: assigns `wt(o)` to each
    symbol in `supp(o)` and `0` elsewhere. These are the generators of the
    parity semimodule. -/
def parityIndicator {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (o : Obs) (a : α) : ℕ :=
  if a ∈ sys.supp o then sys.wt o else 0

/-
The support of the parity indicator vector equals the observable's support
    (when the weight is positive).
-/

/-
Parity indicators recover the support: if two observables have the same
    indicator and positive weights, they have the same support.
-/

/-- A vector is in the parity semimodule if it's a ℕ-linear combination
    of indicator vectors. -/
def InParitySemimodule {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (v : α → ℕ) : Prop :=
  ∃ c : Obs → ℕ, ∀ a : α, v a = ∑ o : Obs, c o * parityIndicator sys o a

/-
Every indicator vector is in the parity semimodule.
-/

/-
The zero vector is in the parity semimodule.
-/

/-! ## §9. Extremal Generators -/

/-- An observable is an **extremal generator** if its support is nonempty and
    its indicator is not expressible as a ℕ-linear combination of indicators
    from other observables (with the observable's own coefficient being zero). -/
def IsExtremalGenerator {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (o : Obs) : Prop :=
  sys.supp o ≠ ∅ ∧
  ¬∃ c : Obs → ℕ, c o = 0 ∧
    ∀ a : α, parityIndicator sys o a = ∑ o' : Obs, c o' * parityIndicator sys o' a

/-- Incomparable supports: no active observable's support is contained in another's.
    This is stronger than separation and ensures extremality of all active observables. -/
def IncomparableSupports {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) : Prop :=
  ∀ o₁ o₂ : Obs, o₁ ≠ o₂ → sys.supp o₁ ≠ ∅ → sys.supp o₂ ≠ ∅ →
    ¬(sys.supp o₁ ⊆ sys.supp o₂)

/-
Incomparable supports with injective empty-support restriction imply separation.
    The incomparability condition handles nonempty supports; we additionally
    need that at most one observable has empty support.
-/

/-
Under incomparable supports with positive weights, every active observable is
    an extremal generator. The proof: if parityIndicator o were a combination of
    others (c o = 0), then for a ∉ supp o the combination must vanish, forcing
    all contributing o' to have supp o' ⊆ supp o, contradicting incomparability.
-/


/-! ## §10. Certified Reconstruction -/

/-- Reconstruct the minimal Tanner hypergraph from closure-parity system data.
    This is the computable certified extraction pipeline. -/
def reconstructMinimalTanner {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) : TannerHypergraph α Obs :=
  canonicalTanner sys



/-! ## §11. Nearest-Codeword Witness -/

/-- A **codeword** is a word whose syndrome is identically zero. -/
def IsCodeword {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (w : α → ℕ) : Prop :=
  ∀ o : Obs, syndrome sys w o = 0



/-! ## §12. Closure-Capacity Bridge -/

/-- The **parity capacity** of a set `S` is the number of active observables
    whose support is contained in `S`. This connects to closure-capacity theory. -/
def parityCapacity {Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs) (S : Finset α) : ℕ :=
  (Finset.univ.filter fun o => sys.supp o ⊆ S ∧ sys.supp o ≠ ∅).card

/-
Parity capacity is monotone: larger sets have at least as many checks.
-/

/-
Parity capacity is closure-invariant: `cap(S) = cap(cl(S))` since
    supports are closed sets.
-/

/-! ## §13. Main Duality Package -/

/-
**Certified Minimal Tanner Reconstruction Theorem**.

Every closure-parity system admits a canonical minimal Tanner realization
with the following properties:
1. It realizes the parity system (supports and weights match)
2. It achieves minimum check-node count among all realizations
3. Syndrome computation factors through its incidence structure
4. It is unique among minimal realizations (up to equivalence)

This is the main duality theorem: decoding objects (Tanner hypergraphs) are
canonical algebraic shadows of closure-parity semantics, not auxiliary
combinatorial artifacts.
-/

/-
**Finite Closure-Parity Semimodule Duality**.

For any closure-parity system with incomparable supports and positive weights,
the parity indicator vectors generate a semimodule whose extremal generators
correspond bijectively to the check nodes of the minimal Tanner realization.
-/

end ClosureSyndromeDecoding


