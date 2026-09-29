-- Prove2me | Definitions.Def_Bridges_ClosureSheafGeneralization
-- name    : Bridges_ClosureSheafGeneralization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:52.507252+00:00
-- url     : https://prove2.me/theorems/c90fdbd2-0bea-45e9-98f7-90d1f0875035
-- title:
--   Aether Catalog definitions — Bridges_ClosureSheafGeneralization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureSheafGeneralization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureSheafGeneralization.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Closure-Sheaf Generalization: Tropical Nerve Descent for Concept Learning

This file formalizes a new bridge between closure systems, sheaf descent, tropical/idempotent
algebra, and certified machine learning generalization. The key insight is that **generalization
can be certified as a sheaf-gluing phenomenon over a finite closure nucleus**, with idempotent
structure replacing linear averaging.

## Main results

* `FinClosureSpace` — Structure for finite closure operators (extensive, monotone, idempotent).
* `ClosurePresheaf` — A presheaf of types over subsets with restriction maps.
* `closure_presheaf_exact_gluing` — Pairwise compatible local sections glue uniquely.
* `closure_global_section_eq_unique_tropical_argmin` — The glued section is the unique
  minimizer of a tropical disagreement functional.
* `certified_generalization_from_closure_nerve_descent` — Generalization bounded by
  empirical error plus tropical extension complexity.
* `closure_consistent_predictor_representation` — Closure-consistent predictors are
  uniquely representable as global sections.

## Proof strategy

We follow **Strategy A (Direct finite descent)**:
1. Define finite presheaf with explicit restriction maps.
2. Express compatibility on pairwise overlaps.
3. Use a finite gluing axiom.
4. Derive existence and uniqueness from gluing + compatibility.
5. Show the tropical functional vanishes exactly on glued sections.
6. Use uniqueness to deduce uniqueness of minimizer.

## Cross-domain significance

- **Sheaf theory × ML**: Training consistency = descent data; hypotheses = global sections.
- **Closure systems × concept learning**: Closure nucleus = concept entailment.
- **Tropical algebra × certified inference**: Sup-aggregation replaces averaging.
- **Nerve topology × generalization**: Depends on overlap combinatorics, not parameter norm.
- **EML × algebraic semantics**: Predictors = semantic sections over concept lattices.
-/

open Set Finset

/-! ## Closure Operator / Nucleus -/

/-- A finite closure space: a closure operator on `Set X` that is extensive, monotone, idempotent.
Encodes concept entailment / feature completion / latent semantic saturation. -/
structure FinClosureSpace (X : Type*) where
  /-- The closure operator -/
  cl : Set X → Set X
  /-- Extensiveness: every set is contained in its closure -/
  extensive : ∀ s, s ⊆ cl s
  /-- Monotonicity: closure preserves subset ordering -/
  monotone : ∀ ⦃s t : Set X⦄, s ⊆ t → cl s ⊆ cl t
  /-- Idempotency: closing a closed set does nothing -/
  idempotent : ∀ s, cl (cl s) = cl s

/-- A set is closed w.r.t. a closure operator if `cl s = s`. -/
def FinClosureSpace.IsClosed {X : Type*} (C : FinClosureSpace X) (s : Set X) : Prop :=
  C.cl s = s



/-! ## Presheaf on Subsets -/

/-- A presheaf of types over subsets of X with restriction maps.
Sections `F V` represent local predictors; restriction maps encode how global
hypotheses restrict to local patches. -/
structure ClosurePresheaf (X : Type*) where
  /-- The type of sections over a subset -/
  F : Set X → Type*
  /-- Restriction map: given W ⊆ V, restrict a section from V to W -/
  res : ∀ {V W : Set X}, W ⊆ V → F V → F W
  /-- Restriction along identity is identity -/
  res_id : ∀ (V : Set X) (x : F V), res (Set.Subset.refl V) x = x
  /-- Restriction composes correctly (functoriality) -/
  res_comp : ∀ {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C) (x : F C),
      res hAB (res hBC x) = res (Set.Subset.trans hAB hBC) x

/-! ## Pairwise Compatibility and Gluing -/

/-- Pairwise compatibility: for each pair (i,j), restrictions to U i ∩ U j agree. -/
def PairwiseCompatible {X I : Type*}
    (P : ClosurePresheaf X) (U : I → Set X) (s : ∀ i, P.F (U i)) : Prop :=
  ∀ i j, P.res (Set.inter_subset_left (s := U i) (t := U j)) (s i)
       = P.res (Set.inter_subset_right (s := U i) (t := U j)) (s j)

/-- The gluing axiom: pairwise compatible local sections uniquely amalgamate
to a global section restricting to each local section. -/
def HasGluingProperty {X I : Type*}
    (P : ClosurePresheaf X) (U : I → Set X) : Prop :=
  ∀ (s : ∀ i, P.F (U i)),
    PairwiseCompatible P U s →
    ∃! g : P.F Set.univ, ∀ i, P.res (Set.subset_univ (U i)) g = s i

/-! ## Theorem 1: Exact Finite Descent (Sheaf Gluing) -/


/-! ## Tropical Disagreement Functional -/

/-- A defect measure comparing local sections. Returns ⊥ iff sections are equal. -/
structure DefectMeasure {X : Type*} (P : ClosurePresheaf X) (α : Type*)
    [LE α] [OrderBot α] where
  /-- The defect function on each local patch -/
  defect : ∀ (V : Set X), P.F V → P.F V → α
  /-- Defect is zero iff sections agree -/
  defect_eq_bot_iff : ∀ (V : Set X) (a b : P.F V), defect V a b = ⊥ ↔ a = b

/-- The tropical extension functional: the supremum of local defects. -/
noncomputable def tropicalExtensionFunctional
    {X I α : Type*} [Fintype I] [SemilatticeSup α] [OrderBot α]
    (P : ClosurePresheaf X) (U : I → Set X)
    (D : DefectMeasure P α)
    (s : ∀ i, P.F (U i)) (g : P.F Set.univ) : α :=
  Finset.sup Finset.univ
    (fun i => D.defect (U i) (P.res (Set.subset_univ (U i)) g) (s i))

/-! ## Auxiliary lemmas for the tropical functional -/

/-
The tropical extension functional is ⊥ iff every local restriction matches.
-/

/-
If a global section restricts correctly, the tropical functional is ⊥.
-/

/-
If the tropical functional is ⊥, then all local restrictions match.
-/

/-! ## Theorem 2: Variational Characterization -/

/-
**Tropical argmin characterization**: The glued section is the unique global section
where the tropical extension functional equals ⊥.

Sheaf-theoretic gluing and tropical optimization coincide: the unique global hypothesis
recovered by descent is exactly the one minimizing worst-case local disagreement.
-/

/-
**Uniqueness of tropical argmin**: If the presheaf has the gluing property,
there is a unique global section at which the tropical functional attains ⊥.
-/

/-! ## Theorem 3: Certified Generalization Bound -/

/-
**Certified generalization from closure nerve descent**: Generalization error ≤
empirical error ⊔ max overlap defect.

This turns sheaf descent into a learning certificate.
-/

/-
**Generalization with nerve depth**: Refined bound incorporating nerve depth.
-/

/-! ## Theorem 4: Representation Theorem -/

/-- A predictor is closure-consistent if it restricts correctly to all patches. -/
def IsClosureConsistent {X I : Type*}
    (P : ClosurePresheaf X) (U : I → Set X) (s : ∀ i, P.F (U i))
    (g : P.F Set.univ) : Prop :=
  ∀ i, P.res (Set.subset_univ (U i)) g = s i

/-
**Closure-consistent predictor representation**: Any predictor consistent with
local training data on each patch is necessarily the unique global section
obtained by sheaf descent.
-/


