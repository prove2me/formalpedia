-- Prove2me | Definitions.Def_Bridges_ClosureCapacitySecretSharingDuality
-- name    : Bridges_ClosureCapacitySecretSharingDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:32.185+00:00
-- url     : https://prove2.me/theorems/5ee95642-6b1f-41a7-b6b0-16eab3527561
-- title:
--   Aether Catalog definitions — Bridges_ClosureCapacitySecretSharingDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureCapacitySecretSharingDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureCapacitySecretSharingDuality.lean by skeleton subtraction
import Mathlib
/-
# Closure-Capacity Secret-Sharing Duality

This module formalizes the bridge between **closure systems with semiring-valued capacities**
and **cryptographic access structures**. The central insight is:

> **Cryptographic authorization can be reconstructed from closure semantics plus
> thresholded information.**

## Main Results

1. **Authorized family is an access structure**: For a monotone, closure-invariant capacity
   on a closure operator, the thresholded authorized family is upward-closed (monotone).

2. **Minimal authorized sets are closure bases**: A set is minimal authorized iff it is
   a basis (irredundant generator) of its closure and meets the capacity threshold.

3. **Realization theorem**: Every finite access structure (with upward-closed authorized
   family and finitely many minimal authorized sets) admits a closure-capacity realization.

4. **Certified reconstruction**: From a finite closure-capacity system, one can extract
   a reconstruction data object that certifies which coalitions are authorized.

## Cross-Domain Connections

- **Cryptography**: Access structures, minimal authorized coalitions, reconstruction
- **Closure Systems / Moore Families**: Closure operators, bases, closed sets
- **Information Theory**: Monotone capacity as information measure, threshold semantics
- **Tropical/Idempotent Algebra**: Capacity as a valuation in ordered semirings

## References

Builds on the closure-secret-sharing duality in
`Bridges.AlgebraEMLCryptography.ClosureSecretSharingDuality` and the p-adic closure
information duality in `Bridges.AlgebraEMLTropical.PadicClosureInformationDuality`.
-/


open Set Function

noncomputable section

namespace Bridges.AlgebraEMLCryptography.ClosureCapacityDuality

/-! ## §1. Core Definitions -/



/-- A set `A` is *authorized* at threshold `t` if `t ≤ cap (cl A)`. -/
def Authorized {α K : Type*} [Preorder K]
    (cl : Set α → Set α) (cap : Set α → K) (t : K) (A : Set α) : Prop :=
  t ≤ cap (cl A)

/-- A set `A` is *minimal authorized* if it is authorized and no proper subset is. -/
def MinimalAuthorized {α K : Type*} [Preorder K]
    (cl : Set α → Set α) (cap : Set α → K) (t : K) (A : Set α) : Prop :=
  Authorized cl cap t A ∧ ∀ B : Set α, B ⊂ A → ¬ Authorized cl cap t B


/-! ## §2. Finite Access Structures -/

/-- A *finite access structure* consists of an upward-closed family of authorized sets
    with finitely many minimal elements. -/
structure FiniteAccessStructure (α : Type*) where
  auth : Set (Set α)
  upward_closed : ∀ {A B : Set α}, A ∈ auth → A ⊆ B → B ∈ auth
  finite_minimals : Set.Finite {A : Set α | A ∈ auth ∧ ∀ B : Set α, B ⊂ A → B ∉ auth}

/-! ## §3. Reconstruction Data -/

/-- Reconstruction data for a secret-sharing scheme: an incidence relation between
    share indices and participants, plus a score function measuring coverage. -/
structure ReconstructionData (α ι : Type*) where
  dealer : ι
  incidence : ι → Set α
  score : Set α → ℕ

/-- A reconstruction data object *correctly reconstructs* an authorization predicate
    at threshold `τ` if `Auth A ↔ τ ≤ R.score A` for all `A`. -/
def Reconstructs {α ι : Type*} (R : ReconstructionData α ι)
    (Auth : Set α → Prop) (τ : ℕ) : Prop :=
  ∀ A : Set α, Auth A ↔ τ ≤ R.score A

/-! ## §4. Theorem 1: Authorized Family Is an Access Structure -/

/-
**Theorem 1a**: The authorized family under a monotone, closure-invariant capacity
    is upward-closed. This follows from monotonicity of `cl` and `cap`:
    if `A ⊆ B` then `cl A ⊆ cl B` hence `cap (cl A) ≤ cap (cl B)`.
-/

/-
Equivalent formulation: the authorized predicate is monotone as a function
    from `Set α` to `Prop` (ordered by implication).
-/

/-! ## §5. Theorem 1b,c: Minimal Authorized Sets and Closure Bases -/

/-
**Theorem 1b**: If `A` is minimal authorized, then `A` is a closure basis for
    `cl A`, i.e., no proper subset of `A` generates the same closure.

    Proof idea: If `B ⊂ A` and `cl B = cl A`, then `cap (cl B) = cap (cl A) ≥ t`,
    contradicting minimality of `A`.
-/

/-
**Theorem 1c**: Conversely, if `B` is a closure basis for `cl B`, the threshold
    is met at `cl B`, and every proper subset has capacity below threshold, then `B`
    is minimal authorized.

    This characterizes minimal authorized sets precisely as threshold-crossing
    closure bases.
-/

/-
The full characterization: `A` is minimal authorized iff `A` is authorized
    and every proper subset has capacity below threshold.
    (This is essentially the definition, but phrased as a clean iff.)
-/


/-! ## §6. Theorem 2: Realization of Finite Access Structures -/

/-
Given a finite access structure, construct a closure operator from its
    authorized family: `cl_𝒜 A` is the intersection of all supersets of `A`
    that are "authorization-saturated". In the boolean case, we use the identity
    closure (which trivially satisfies all closure axioms) and define `cap`
    via the authorized family.
-/

/-! ## §7. Theorem 3: Certified Reconstruction -/

/-
**Theorem 3**: From a finite closure-capacity system with ℕ-valued capacity,
    one can extract a reconstruction data object. We construct it using the set
    of minimal authorized sets as share indices, with the score counting how many
    minimal authorized sets are covered (have their elements contained in the coalition).

    The key insight is that in a monotone access structure, `A` is authorized iff
    it contains some minimal authorized set.
-/

/-! ## §8. Closure-Capacity Morphisms and Faithfulness -/

/-- A morphism between closure-capacity systems: a function that preserves
    closure structure and does not increase capacity. -/
structure ClosureCapacityHom
    {α β K : Type*} [Preorder K]
    (clα : Set α → Set α) (capα : Set α → K)
    (clβ : Set β → Set β) (capβ : Set β → K) where
  toFun : α → β
  map_closed : ∀ A : Set α, image toFun (clα A) ⊆ clβ (image toFun A)
  map_capacity : ∀ A : Set α, capα (clα A) ≤ capβ (clβ (image toFun A))

/-
Two closure-capacity homomorphisms are equal iff their underlying functions agree.
-/

/-
Morphisms preserve authorized status: if `A` is authorized in the source,
    then `f(A)` is authorized in the target.
-/

/-! ## §9. Submodularity Strengthening -/

/-- A capacity is *submodular on closures* if the standard submodularity
    inequality holds when applied through the closure operator. -/
def SubmodularOnClosures {α : Type*}
    (cl : Set α → Set α) (cap : Set α → ℕ) : Prop :=
  ∀ A B : Set α,
    cap (cl (A ∪ B)) + cap (cl (A ∩ B)) ≤ cap (cl A) + cap (cl B)

/-
Under submodularity, if two sets are both unauthorized but their union is authorized,
    then combining them strictly increases capacity beyond what each contributes alone.
    This is a weak form of the "exchange" property for threshold-crossing.
-/

/-! ## §10. Capacity on Closed Sets -/

/-
A closure-invariant capacity factors through a well-defined function on closed
    sets. This is the key structural lemma enabling the passage from set-level to
    lattice-level reasoning.
-/

end Bridges.AlgebraEMLCryptography.ClosureCapacityDuality


