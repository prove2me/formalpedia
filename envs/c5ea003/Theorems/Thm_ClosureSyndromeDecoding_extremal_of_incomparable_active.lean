-- Prove2me | Theorems.Thm_ClosureSyndromeDecoding_extremal_of_incomparable_active
-- name    : ClosureSyndromeDecoding.extremal_of_incomparable_active
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:40:35.193046+00:00
-- url     : https://prove2.me/theorems/26899d23-e1de-49c4-9d68-3825910510bc
-- title:
--   Extremal of incomparable active
-- statement:
--   Formal statement of `ClosureSyndromeDecoding.extremal_of_incomparable_active` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ClosureSyndromeDecoding.extremal_of_incomparable_active{Obs : Type*} [Fintype Obs] [DecidableEq Obs]
--       (sys : ClosureParitySystem α Obs)
--       (hinc : IncomparableSupports sys)
--       (hwt : ∀ o, sys.supp o ≠ ∅ → sys.wt o ≠ 0)
--       (o : Obs) (ho : o ∈ sys.activeObs) :
--       IsExtremalGenerator sys o := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ClosureSyndromeDecodingDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ClosureSyndromeDecodingDuality.lean#L399

-- Thm stub generated from Bridges/ClosureSyndromeDecodingDuality.lean
import Mathlib
import Definitions.Def_Bridges_ClosureSyndromeDecodingDuality

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

open ClosureSyndromeDecoding

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## §1. Finite Closure Operators -/


open FinClosureOp

variable {α : Type*} [Fintype α] [DecidableEq α] (C : FinClosureOp α)







/-! ## §2. Closure-Parity Systems -/


open ClosureParitySystem

variable {α Obs : Type*} [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs]







/-! ## §3. Tanner Hypergraphs -/


open TannerHypergraph

variable {α Obs : Type*} [Fintype α] [DecidableEq α] [Fintype Obs] [DecidableEq Obs]






/-! ## §4. Canonical Tanner Construction -/


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


/-
The support of the parity indicator vector equals the observable's support
    (when the weight is positive).
-/

/-
Parity indicators recover the support: if two observables have the same
    indicator and positive weights, they have the same support.
-/


/-
Every indicator vector is in the parity semimodule.
-/

/-
The zero vector is in the parity semimodule.
-/

/-! ## §9. Extremal Generators -/



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

theorem ClosureSyndromeDecoding.extremal_of_incomparable_active{Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs)
    (hinc : IncomparableSupports sys)
    (hwt : ∀ o, sys.supp o ≠ ∅ → sys.wt o ≠ 0)
    (o : Obs) (ho : o ∈ sys.activeObs) :
    IsExtremalGenerator sys o := by sorry
