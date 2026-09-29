-- Prove2me | solution 1 for ClosureSyndromeDecoding.extremal_of_incomparable_active
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:10:49.093588+00:00
-- url     : https://prove2.me/submissions/5926a91d-f364-45fa-a4a4-56ee63f168e6

-- Sol generated from Bridges/ClosureSyndromeDecodingDuality.lean
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


/-! ## §10. Certified Reconstruction -/




/-! ## §11. Nearest-Codeword Witness -/




/-! ## §12. Closure-Capacity Bridge -/


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


open ClosureSyndromeDecoding in
theorem solution{Obs : Type*} [Fintype Obs] [DecidableEq Obs]
    (sys : ClosureParitySystem α Obs)
    (hinc : IncomparableSupports sys)
    (hwt : ∀ o, sys.supp o ≠ ∅ → sys.wt o ≠ 0)
    (o : Obs) (ho : o ∈ sys.activeObs) :
    IsExtremalGenerator sys o := by
  -- By definition of `activeObs`, we know that `sys.supp o ≠ ∅`.
  have h_supp_ne_empty : sys.supp o ≠ ∅ := by
    exact Finset.mem_filter.mp ho |>.2;
  refine' ⟨ h_supp_ne_empty, _ ⟩;
  intro ⟨ c, hc₀, hc ⟩
  have h_contra : ∀ o' ≠ o, c o' ≠ 0 → sys.supp o' ⊆ sys.supp o := by
    intro o' ho' hc'
    have h_contra : ∀ a ∈ sys.supp o', parityIndicator sys o a ≠ 0 := by
      intro a ha
      have h_contra : parityIndicator sys o a ≥ c o' * parityIndicator sys o' a := by
        exact hc a ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le ( c x * parityIndicator sys x a ) ) ( Finset.mem_univ o' );
      simp_all +decide [ parityIndicator ];
      exact ⟨ o', ha, hc', hwt o' ( by aesop ) ⟩;
    unfold parityIndicator at h_contra; aesop;
  -- Since `sys.supp o` is nonempty, there exists some `a ∈ sys.supp o`.
  obtain ⟨a, ha⟩ : ∃ a, a ∈ sys.supp o := by
    exact Finset.nonempty_of_ne_empty h_supp_ne_empty;
  specialize hc a; simp_all +decide [ parityIndicator ] ;
  rw [ Finset.sum_eq_single o ] at hc <;> simp_all +decide [ Finset.sum_ite ];
  exact fun o' ho' ha' => Classical.or_iff_not_imp_left.2 fun h => False.elim <| hinc o' o ho' ( by aesop ) h_supp_ne_empty <| h_contra o' ho' h |> fun h => by aesop;
