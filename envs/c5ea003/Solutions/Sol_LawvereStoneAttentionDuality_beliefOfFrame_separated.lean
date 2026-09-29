-- Prove2me | solution 1 for LawvereStoneAttentionDuality.beliefOfFrame_separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:54:01.12417+00:00
-- url     : https://prove2.me/submissions/e37f945c-d57a-40d9-8c01-f1957c7855c0

-- Sol generated from Bridges/LawvereStoneAttentionDuality.lean
import Mathlib
import Definitions.Def_Bridges_LawvereStoneAttentionDuality
/-
# Lawvere–Stone Duality for Finite Idempotent Belief Semimodules and Attention Frames

This file establishes a finite duality between **belief semimodules** (finite structures
equipped with closure operators, Lawvere pseudo-metrics, and enriched observables over a
finite complete lattice serving as an idempotent semiring) and **attention frames** (finite
weighted frames whose semantics reconstructs belief states from observable weights).

## Mathematical Overview

The duality is based on the enriched Yoneda paradigm for finite Lawvere metric spaces.
Given a finite complete lattice `S` (modeling an idempotent semiring via `⊔` as addition),
a **belief semimodule** `M` is a finite type with:
- an `S`-valued Lawvere pseudo-metric `d : M → M → S`,
- a closure operator `cl : M → M` that is idempotent and nonexpansive.

The **attention spectrum** `Spec(M)` consists of closure-stable nonexpansive observables
`M → S`. Conversely, an **attention frame** `F` defines belief states as nonexpansive
functions `F → S`.

The main duality theorem states that under separation conditions, these constructions
are mutually inverse up to isomorphism. The certified minimal attention reconstruction
theorem shows that from generators of `M`, one obtains a unique (up to cardinality)
minimal attention frame realizing the observable kernel.

## Main Results

* `evalProfile_injective` — evaluation map is injective for separated semimodules.
* `obsKernel_self`, `obsKernel_tri` — observable kernel satisfies Lawvere metric axioms.
* `minimalFrame_realizes` — the minimal frame realizes the observable kernel.
* `minimalFrame_is_minimal` — the minimal frame has minimal cardinality.
* `certified_minimal_attention_reconstruction` — existence of a minimal realizer with
  correct cardinality matching generators.
* `minimal_realizer_card_eq` — any two minimal realizers have the same cardinality.
* `finite_lawvere_stone_attention_duality` — the main duality packaging.

## Cross-Domain Connections

This builds explicitly on the duality patterns established in:
- `certified_reconstruction_from_closure_capacity` (Catalog): reconstruction of finite
  algebraic structure from observable capacity data.
- `finite_closure_extractor_spectrum_duality` (Catalog): finite closure/spectrum duality
  upgraded here from closure-only semantics to closure + Lawvere metric + residuated
  observables.

### Enriched Category Theory / Lawvere Metrics
The attention kernel is a finite Lawvere-enriched relation. The reconstruction theorem
says: attention architectures are recoverable from enriched observable semantics.

### Stone Duality / Semantics of Tests
The spectrum of attention tests is a Stone-style dual object: what the architecture can
be observed to do is mathematically dual to what the architecture is.

### Tropical/Idempotent Algebra
Using a lattice (modeling an idempotent semiring) makes attention weights compositional
via sup-linearity. This connects to shortest-path algebra and max-plus systems.

### Certified Architecture Compression
Minimality of `F_min(K)` means semantics-driven compression is a theorem: the observable
kernel determines the unique minimal attention realization.
-/


noncomputable section

open Function Finset

open LawvereStoneAttentionDuality

universe u v

variable (S : Type u) [CompleteLattice S] [DecidableEq S]

/-! ## §1. Finite Belief Semimodule

A **finite belief semimodule** over a complete lattice `S` packages:
- a finite carrier type `M`,
- a closure operator `cl : M → M` (idempotent),
- a Lawvere pseudo-metric `d : M → M → S` (reflexive, triangle inequality),
- nonexpansiveness of closure w.r.t. the metric.
-/


/-! ## §2. Attention Observables -/


/-! ## §3. Separation and Evaluation -/




/-! ## §4. Finite Attention Frames -/


/-! ## §5. Observable Kernel -/




/-! ## §6. Minimal Frame Construction -/


/-! ## §7. Generation and Realization -/



/-! ## §8. The Minimal Frame Realizes the Observable Kernel -/



/-! ## §9. Minimality: Lower Bound on Realizer Cardinality -/


/-! ## §10. Belief Semimodule from Attention Frame -/


/-! ## §11. Roundtrip: Frame → Belief → Frame -/


/-! ## §12. Roundtrip: Belief → Frame → Belief -/


/-! ## §13. Certified Minimal Attention Reconstruction -/

/-
**Certified Minimal Attention Reconstruction.**
For every finite belief semimodule `B` with generating family `e`, there exists a
minimal attention frame `Fr` such that:
1. `Fr` realizes the observable kernel,
2. Any other realizer has at least as many tokens,
3. `Fr` has token type equivalent to the generator type.
-/

/-! ## §14. Separation for Frames with Distinguishing Weights -/


/-! ## §15. Observable Kernel Properties -/



/-! ## §16. Main Duality Packaging -/

/-
**Finite Lawvere–Stone Attention Duality.**

For a finite separated belief semimodule `B` with generating family `e`:
1. The evaluation profile is injective (Stone-style embedding).
2. The minimal frame realizes the observable kernel.
3. The roundtrip Belief → Frame → Belief preserves the metric on generators.
4. The roundtrip Frame → Belief → Frame recovers the kernel.
5. Separation of frames yields separation of belief semimodules.
-/

/-! ## §17. Structural Parallel with Closure-Extractor Duality -/



open LawvereStoneAttentionDuality in
omit [DecidableEq S] in
/-
A frame with separating weights yields a separated belief semimodule.
-/
theorem solution{F : Type v} (Fr : FinAttFrame S F)
    (hsep : ∀ s t : F, (∀ u, Fr.w s u = Fr.w t u) → s = t) :
    Separated S (beliefOfFrame S Fr) := by
  intro s t h;
  contrapose! hsep;
  refine' ⟨ t, s, _, hsep.symm ⟩;
  intro u;
  refine' le_antisymm _ _;
  · have := h ⟨ fun x => Fr.w t x, ?_, ?_ ⟩;
    all_goals norm_num [ beliefOfFrame ];
    all_goals norm_num [ AttObs ] at *;
    · have := Fr.w_tri t s u; simp_all +decide [ FinAttFrame.w_self ] ;
    · exact fun x y => Fr.w_tri t x y;
  · specialize h ⟨ fun x => Fr.w s x, ?_, ?_ ⟩;
    all_goals norm_num [ beliefOfFrame ] at *;
    · exact fun x y => Fr.w_tri s x y;
    · have := Fr.w_tri s t u;
      rw [ ← h ] at this;
      rw [ Fr.w_self ] at this ; aesop
