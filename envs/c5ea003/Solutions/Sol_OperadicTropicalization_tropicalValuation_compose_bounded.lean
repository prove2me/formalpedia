-- Prove2me | solution 1 for OperadicTropicalization.tropicalValuation_compose_bounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T11:11:12.915779+00:00
-- url     : https://prove2.me/submissions/818de8df-2c8b-4b02-ba2f-de06049ee3ae

-- Sol generated from Bridges/OperadicTropicalization.lean
import Mathlib
import Definitions.Def_Bridges_OperadicTropicalization

/-!
# Operadic Tropicalization of Neural Architectures

This file establishes a formal bridge between **operad theory**, **tropical algebra**, and
**neural architecture classification**. The central result is a certified tropical
reconstruction theorem: bounded neural architectures admit complete tropical operadic
invariants that classify them up to structural congruence.

## Main Results

### Structures and Definitions
* `ArchExpr` — tree-structured operadic expressions (free operad elements)
* `TropicalArchProfile` — tropical complexity profile with depth, width, generator count
* `StructuralCongr` — structural congruence on architecture expressions
* `tropicalValuation` — the operadic tropical valuation functor
* `ArchitectureSkeleton` — canonical skeleton type for architecture reconstruction
* `reconstructSkeleton` — reconstruction of canonical skeleton from tropical profile

### Key Theorems
* `tropicalValuation_compose` — functoriality under sequential composition
* `tropicalValuation_parallel` — functoriality under parallel composition
* `seqMul_tropAdd_distrib_left` — tropical semiring distributivity
* `tropicalValuation_structural_congr` — invariance under structural congruence
* `depth_width_genCount_tradeoff` — depth × width ≥ generatorCount
* `certified_operadic_tropical_reconstruction` — the main reconstruction theorem
* `tropical_profile_complete_for_bounded_architecture_congruence` — completeness

## Bridge: connects operad theory (compositional syntax) → tropical algebra (min-plus) →
   ML architecture theory (depth/width classification) → automata theory (Myhill–Nerode) →
   certified compression (canonical minimization)

## References
- Loday, Vallette: "Algebraic Operads"
- Maclagan, Sturmfels: "Introduction to Tropical Geometry"
- Cohen, Gaubert, Quadrat: "Max-plus algebra and system theory"
-/

noncomputable section

open OperadicTropicalization

/-! ## Section 1: Architecture Expressions (Free Operad)

An `ArchExpr` is an element of the free operad on one generator, representing
a neural architecture built from:
- `generator`: a single computation module (layer, attention head, etc.)
- `identity`: the identity/pass-through operation
- `compose`: sequential composition (depth increases additively)
- `parallel`: parallel composition (width increases additively)
-/


open ArchExpr








/-! ### Basic structural lemmas -/











/-! ### kChain and wideParallel profile lemmas -/






/-
**Depth-width-generator tradeoff**: the product of depth and max width
    is at least the generator count. This is the operadic analogue of the
    circuit complexity lower bound: you need enough "area" to fit all generators.

    Bridge: connects tropical geometry (area of Newton polytope) to circuit
    complexity (depth × width lower bounds).
-/


/-! ## Section 2: Tropical Architecture Profile

The `TropicalArchProfile` is the tropical codomain of the valuation functor.
It carries two composition operations (sequential and parallel) corresponding
to the two operadic compositions, and a tropical addition (component-wise min)
making it an idempotent semiring-like structure. -/


open TropicalArchProfile







/-! ### Sequential composition monoid laws -/




/-! ### Parallel composition commutative monoid laws -/





/-! ### Tropical addition semilattice laws -/




/-! ### Tropical distributivity

The key tropical semiring law: sequential composition distributes over
tropical addition. This is the operadic analogue of the fundamental
property `a + min(b,c) = min(a+b, a+c)` in tropical arithmetic.

Bridge: connects idempotent semiring theory to certified architecture optimization —
composing with the "best of two alternatives" equals the best of the two compositions. -/




/-! ## Section 3: The Tropical Valuation Functor

The tropical valuation maps architecture expressions to their tropical profiles.
It is functorial with respect to both sequential and parallel composition:
this is the core "functor" property that makes the valuation useful for
classification. -/






/-- **Subadditivity of generator count**: compose never creates generators. -/
theorem tropicalValuation_genVal_compose (e₁ e₂ : ArchExpr) :
    (tropicalValuation (.compose e₁ e₂)).genVal =
    (tropicalValuation e₁).genVal + (tropicalValuation e₂).genVal := by
  simp [tropicalValuation]

/-- **Depth additivity**: sequential composition adds depths. -/
theorem tropicalValuation_depth_compose (e₁ e₂ : ArchExpr) :
    (tropicalValuation (.compose e₁ e₂)).depthVal =
    (tropicalValuation e₁).depthVal + (tropicalValuation e₂).depthVal := by
  simp [tropicalValuation]


/-! ## Section 4: Structural Congruence

The structural congruence on architecture expressions captures the algebraic
rewriting rules of operadic composition: associativity, identity laws, and
commutativity of parallel composition. This is the operadic analogue of
the Myhill–Nerode equivalence.

Bridge: connects operad theory (presentation by generators and relations)
to automata theory (state equivalence) to certified ML compression
(architecture normalization). -/



/-
**The tropical valuation is invariant under structural congruence.**
    This is the central soundness theorem: operadic rewrites do not change
    the tropical complexity profile.

    Bridge: connects operad presentation theory to tropical invariant theory —
    the valuation is a well-defined function on the quotient operad.
-/

/-! ## Section 5: Profile Congruence and Completeness

The profile congruence identifies two expressions when they have the same
tropical profile. The key theorems:
1. Structural congruence implies profile congruence (soundness).
2. Profile congruence is a complete invariant within bounded classes. -/





/-! ## Section 6: Bounded Architecture Classification

For bounded architecture classes (bounded depth, width, generator count),
the tropical profile takes values in a finite set. This enables finite
classification: there are only finitely many distinct tropical signatures
in any bounded class.

Bridge: connects tropical geometry (finite Newton polytopes) to
circuit complexity (bounded circuit classification). -/



/-
The bounded profile set has at most (D+1)*(W+1)*(G+1) elements.
-/

/-
The tropical valuation of a bounded expression lies in the bounded profile set.
    This is the key finiteness theorem: bounded architectures have bounded profiles.
-/


/-! ## Section 7: Canonical Skeleton and Reconstruction

The canonical skeleton is the tropical profile itself. Reconstruction
from the profile is the identity on profiles. The key theorems establish
that this reconstruction is well-defined, unique, and invariant under
both structural and profile congruence.

Bridge: connects tropical reconstruction (recovering a polytope from
its tropicalization) to ML architecture compression (canonical form). -/







/-! ## Section 8: Main Reconstruction Theorems

These are the culminating results: certified operadic tropical reconstruction
for bounded architecture classes. -/




/-! ## Section 9: Composition Bounds and Architecture Complexity

Additional structural theorems relating architecture complexity measures
through tropical valuation properties. -/

/-
Sequential composition preserves bounded class membership.
-/

/-
Parallel composition preserves bounded class membership.
-/

/-
The tropical valuation of a sequential composition is bounded by the
    sequential product of the individual bounds.
-/

/-
**Depth-width tradeoff for profiles**: profile depth × width ≥ generators.
    This is the profile-level formulation of the fundamental complexity bound.
-/


open OperadicTropicalization in
theorem solution{e₁ e₂ : ArchExpr} {G₁ G₂ D₁ D₂ W₁ W₂ : ℕ}
    (h₁ : InBoundedClass e₁ G₁ D₁ W₁) (h₂ : InBoundedClass e₂ G₂ D₂ W₂) :
    (tropicalValuation (.compose e₁ e₂)).depthVal ≤ D₁ + D₂ ∧
    (tropicalValuation (.compose e₁ e₂)).widthVal ≤ max W₁ W₂ ∧
    (tropicalValuation (.compose e₁ e₂)).genVal ≤ G₁ + G₂ := by
  exact ⟨ by
    convert Nat.add_le_add h₁.2.1 h₂.2.1 using 1;
    convert tropicalValuation_depth_compose e₁ e₂ using 1;
    have h_depth_val : ∀ e : ArchExpr, e.depth = (tropicalValuation e).depthVal := by
      intro e; induction e <;> aesop;
    rw [h_depth_val, h_depth_val], by
    -- The width of the composition is the maximum of the widths of the two expressions.
    have h_width : (tropicalValuation (.compose e₁ e₂)).widthVal = max (tropicalValuation e₁).widthVal (tropicalValuation e₂).widthVal := by
      rfl;
    obtain ⟨ _, _, _ ⟩ := h₁; obtain ⟨ _, _, _ ⟩ := h₂;
    rename_i h₁ h₂ h₃ h₄ h₅ h₆;
    refine' h_width.trans_le ( max_le_max _ _ );
    · refine' le_trans _ h₃;
      have h_width_le : ∀ e : ArchExpr, (tropicalValuation e).widthVal ≤ e.maxWidth := by
        intro e; induction' e with e₁ e₂ ih₁ ih₂; aesop;
        · rfl;
        · exact max_le_max ih₁ ih₂;
        · rename_i e₁ e₂ ih₁ ih₂;
          exact le_trans ( by aesop ) ( add_le_add ih₁ ih₂ );
      exact h_width_le e₁;
    · refine' le_trans _ h₆;
      have h_width_le : ∀ e : ArchExpr, (tropicalValuation e).widthVal ≤ e.maxWidth := by
        intro e; induction' e with e₁ e₂ ih₁ ih₂; aesop;
        · rfl;
        · exact max_le_max ih₁ ih₂;
        · rename_i e₁ e₂ ih₁ ih₂;
          exact le_trans ( by aesop ) ( add_le_add ih₁ ih₂ );
      exact h_width_le e₂, by
    convert Nat.add_le_add h₁.1 h₂.1 using 1;
    convert tropicalValuation_genVal_compose e₁ e₂ using 1;
    congr! 1;
    · have h_genCount : ∀ e : ArchExpr, e.generatorCount = (tropicalValuation e).genVal := by
        intro e; induction e <;> aesop;
      exact h_genCount e₁;
    · have h_gen_count : ∀ e : ArchExpr, e.generatorCount = (tropicalValuation e).genVal := by
        intro e; induction e <;> aesop;
      exact h_gen_count e₂ ⟩
