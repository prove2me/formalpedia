-- Prove2me | solution 1 for GLPLogic.loeb_valid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:54.030133+00:00
-- url     : https://prove2.me/submissions/39b8a0ad-0e96-41bb-a64f-2c4af19bab57

-- Sol generated from Logic/ProvabilityLogic/GLPFrames.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_GLPFrames
/-
  # Polymodal Provability Logic (GLP): Frames, Morphisms, and Products

  This file extends provability logic GL to the **polymodal** setting (GLP) and
  develops the **category-theoretic structure** of GL frames:

  1. **GLP Frames**: ℕ-indexed nested hierarchies R₀ ⊇ R₁ ⊇ R₂ ⊇ ··· of GL
     accessibility relations, modeling iterated provability predicates.
  2. **P-Morphisms**: Bounded morphisms — the canonical notion of structure-preserving
     map that reflects modal truth bidirectionally.
  3. **Products and Coproducts**: GL frames are closed under synchronized products
     and disjoint unions.
  4. **Order-Theoretic Bridge**: GL frames = well-founded strict partial orders.

  ## Mathematical Context

  GLP (Japaridze, 1986) models the hierarchy of provability predicates
  Prv₀, Prv₁, Prv₂, ... where Prvₙ₊₁ is provability in a system with
  n-consistency. The frame condition R₀ ⊇ R₁ ⊇ ··· means stronger provability
  sees fewer worlds. P-morphisms are the standard morphisms in modal model theory;
  the truth lemma shows they preserve and reflect forcing, making them the right
  arrows for a category of GL frames.
-/


open GLPLogic

/-! ## Modal Formulas -/


open MFormula
variable {α : Type*}



/-! ## GL Frames -/




/-! ## Core GL Theorems -/

-- !-- Irreflexivity follows from converse well-foundedness: a self-loop
--     w R w would give an infinite ascending chain w, w, w, ···. -- !--

-- !-- Löb's axiom: well-founded induction on the converse of R. Given
--     w ⊩ □(□φ→φ), for any v with wRv, the IH gives v ⊩ □φ, then
--     the hypothesis gives v ⊩ □φ→φ, yielding v ⊩ φ. -- !--



-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: GLP FRAME HIERARCHY
-- Each level of a GLP frame is a valid GL frame. Combined with cross-level
-- antisymmetry, this shows GLP frames are strictly stratified towers.
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Part 1: GLP Frames -/










-- !-- [B]oundary: Without nesting, we have independent GL frames — no cross-level
--     interaction. With nesting, cross-level cycles become impossible (glp_no_cross_cycle).
--     Without transitivity, irreflexivity fails: {w} with R w w is converse well-founded
--     on a finite set but reflexive. -- !--

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 2: P-MORPHISM TRUTH LEMMA
-- P-morphisms preserve and reflect forcing under pullback valuation.
-- This is the semantic backbone of GL model theory.
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Part 2: P-Morphisms (Bounded Morphisms) -/


-- !-- The truth lemma is proved by structural induction on φ. The key case is box:
--     (→) uses back: if M₂, f(w) sees u, lift to v in M₁ with f(v) = u, apply IH.
--     (←) uses forth: if M₁, w sees v, then M₂, f(w) sees f(v), apply IH. -- !--








-- !-- [B]oundary: A mere homomorphism (forth only, no back) does NOT reflect □.
--     Example: M₁ has w→v, M₂ has u (isolated). Map f(w)=f(v)=u. Then M₂,u ⊩ □⊥
--     (vacuously) but M₁,w ⊮ □⊥ (v is accessible and ⊥ fails at v). -- !--

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 3: PRODUCTS AND COPRODUCTS OF GL FRAMES
-- GL frames are closed under synchronized products and disjoint unions.
-- The second incompleteness theorem propagates through both constructions.
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Part 3: Products and Coproducts -/

-- !-- Product: transitivity is componentwise. Well-foundedness of the product
--     relation follows from being a subrelation of the first projection.
--     An infinite product chain projects to an infinite chain in component 1. -- !--




/-- **[E]xample**: Product of trivial frames. -/
example : (GLFrame.prod
    ⟨ℕ, fun _ _ => False, fun h => h.elim,
     ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩⟩
    ⟨ℕ, fun _ _ => False, fun h => h.elim,
     ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩⟩).W = (ℕ × ℕ) := rfl





-- !-- [B]oundary: The synchronized product requires BOTH components to step.
--     If one component is terminal, every product world is terminal.
--     The "interleaving product" (either component steps) is not transitive.
--     Infinite products of finite GL frames produce infinite frames, losing
--     the finite model property crucial for decidability of GL. -- !--

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 4: GL FRAME ↔ WELL-FOUNDED STRICT PARTIAL ORDER
-- The order-theoretic bridge connecting provability logic to order theory.
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Part 4: Order-Theoretic Bridge -/


-- !-- The bridge: GL frames and WFSPOs are definitionally the same structure.
--     A GL frame has R transitive + converse WF → R is irreflexive (proved above).
--     A WFSPO has lt irreflexive + transitive + converse WF → it's a GL frame.
--     This means all of order theory applies to GL frames. -- !--








-- !-- [B]oundary: Dense linear orders like (ℚ, <) do NOT give GL frames because
--     the converse relation (>) is not well-founded: the sequence 1, 1/2, 1/3, ...
--     is infinite strictly decreasing. GL frames correspond exactly to well-founded
--     partial orders, which excludes all dense orders and all infinite chains. -- !--


open GLPLogic in
theorem solution{α : Type*} (M : GLFrame) (V : α → M.W → Prop)
    (φ : MFormula α) (w : M.W)
    (h : forces M V w (.box (.imp (.box φ) φ))) :
    forces M V w (.box φ) := by
  intro v hwv
  induction v using M.R_wf.induction with
  | _ v ih => exact h v hwv (fun t hut => ih t hut (M.R_trans hwv hut))
