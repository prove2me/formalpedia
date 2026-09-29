-- Prove2me | Definitions.Def_Logic_ProvabilityLogic_GLPFrames
-- name    : Logic_ProvabilityLogic_GLPFrames
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:03:10.035226+00:00
-- url     : https://prove2.me/theorems/35abcf65-0407-4629-8483-40c3dfaa576f
-- title:
--   Aether Catalog definitions — Logic_ProvabilityLogic_GLPFrames
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProvabilityLogic.GLPFrames`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProvabilityLogic/GLPFrames.lean by skeleton subtraction
import Mathlib
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


namespace GLPLogic

/-! ## Modal Formulas -/

/-- Modal formulas over propositional variables of type α. -/
inductive MFormula (α : Type*) : Type _
  | var : α → MFormula α
  | bot : MFormula α
  | imp : MFormula α → MFormula α → MFormula α
  | box : MFormula α → MFormula α

namespace MFormula
variable {α : Type*}

def neg (φ : MFormula α) : MFormula α := .imp φ .bot
def con : MFormula α := neg (.box .bot)

end MFormula

/-! ## GL Frames -/

/-- A **GL frame**: transitive, converse well-founded accessibility relation. -/
structure GLFrame where
  W : Type*
  R : W → W → Prop
  R_trans : ∀ {u v w : W}, R u v → R v w → R u w
  R_wf : WellFounded (Function.swap R)

/-- Kripke forcing relation. -/
def forces {α : Type*} (M : GLFrame) (V : α → M.W → Prop) :
    M.W → MFormula α → Prop
  | w, .var p => V p w
  | _, .bot => False
  | w, .imp φ ψ => forces M V w φ → forces M V w ψ
  | w, .box φ => ∀ v, M.R w v → forces M V v φ

/-- Frame validity: φ holds at every world under every valuation. -/
def GLFrame.valid {α : Type*} (M : GLFrame) (φ : MFormula α) : Prop :=
  ∀ (V : α → M.W → Prop) (w : M.W), forces M V w φ

/-! ## Core GL Theorems -/

-- !-- Irreflexivity follows from converse well-foundedness: a self-loop
--     w R w would give an infinite ascending chain w, w, w, ···. -- !--
theorem GLFrame.irrefl (M : GLFrame) (w : M.W) : ¬M.R w w := by
  intro h; exact (M.R_wf.irrefl).irrefl w h

-- !-- Löb's axiom: well-founded induction on the converse of R. Given
--     w ⊩ □(□φ→φ), for any v with wRv, the IH gives v ⊩ □φ, then
--     the hypothesis gives v ⊩ □φ→φ, yielding v ⊩ φ. -- !--



-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREM 1: GLP FRAME HIERARCHY
-- Each level of a GLP frame is a valid GL frame. Combined with cross-level
-- antisymmetry, this shows GLP frames are strictly stratified towers.
-- ═══════════════════════════════════════════════════════════════════════════

/-! ## Part 1: GLP Frames -/

/-- A **GLP frame**: ℕ-indexed nested family R₀ ⊇ R₁ ⊇ R₂ ⊇ ···,
    each transitive and converse well-founded.

    The nesting R_{n+1} ⊆ R_n means stronger provability sees fewer worlds:
    if something is provable by a stronger system, it's provable by a weaker one. -/
structure GLPFrame where
  W : Type*
  R : ℕ → W → W → Prop
  R_trans : ∀ n, ∀ {u v w : W}, R n u v → R n v w → R n u w
  R_wf : ∀ n, WellFounded (Function.swap (R n))
  R_nest : ∀ n {u v : W}, R (n + 1) u v → R n u v

/-- **[P]roof**: Extract the GL frame at level n from a GLP frame. -/
def GLPFrame.level (F : GLPFrame) (n : ℕ) : GLFrame where
  W := F.W
  R := F.R n
  R_trans := F.R_trans n
  R_wf := F.R_wf n








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

/-- A **p-morphism** (bounded morphism) f : M₁ → M₂ satisfies:
    - **Forth**: R₁(w,v) → R₂(f(w), f(v))
    - **Back**: R₂(f(w), u) → ∃ v, R₁(w,v) ∧ f(v) = u -/
structure PMorphism (M₁ M₂ : GLFrame) where
  f : M₁.W → M₂.W
  forth : ∀ {w v : M₁.W}, M₁.R w v → M₂.R (f w) (f v)
  back : ∀ {w : M₁.W} {u : M₂.W}, M₂.R (f w) u → ∃ v, M₁.R w v ∧ f v = u

-- !-- The truth lemma is proved by structural induction on φ. The key case is box:
--     (→) uses back: if M₂, f(w) sees u, lift to v in M₁ with f(v) = u, apply IH.
--     (←) uses forth: if M₁, w sees v, then M₂, f(w) sees f(v), apply IH. -- !--




/-- **[E]xample**: Composition of p-morphisms. -/
def PMorphism.comp {M₁ M₂ M₃ : GLFrame}
    (p : PMorphism M₁ M₂) (q : PMorphism M₂ M₃) : PMorphism M₁ M₃ where
  f := q.f ∘ p.f
  forth h := q.forth (p.forth h)
  back h := by
    obtain ⟨v₂, hv₂, rfl⟩ := q.back h
    obtain ⟨v₁, hv₁, rfl⟩ := p.back hv₂
    exact ⟨v₁, hv₁, rfl⟩




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

/-- **[P]roof — Product GL Frame**: Synchronized product with componentwise R.
    R((w₁,w₂),(v₁,v₂)) iff R₁(w₁,v₁) ∧ R₂(w₂,v₂). -/
def GLFrame.prod (M₁ M₂ : GLFrame) : GLFrame where
  W := M₁.W × M₂.W
  R := fun w v => M₁.R w.1 v.1 ∧ M₂.R w.2 v.2
  R_trans := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨M₁.R_trans h1 h3, M₂.R_trans h2 h4⟩
  R_wf := by
    apply Subrelation.wf (r := InvImage (Function.swap M₁.R) Prod.fst)
    · intro a b ⟨h1, _⟩; exact h1
    · exact InvImage.wf Prod.fst M₁.R_wf







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

/-- A **well-founded strict partial order**: irreflexive, transitive, converse
    well-founded. These are exactly GL frames under a different presentation. -/
structure WFSPO where
  carrier : Type*
  lt : carrier → carrier → Prop
  lt_irrefl : ∀ x, ¬lt x x
  lt_trans : ∀ {x y z}, lt x y → lt y z → lt x z
  lt_wf : WellFounded (Function.swap lt)

-- !-- The bridge: GL frames and WFSPOs are definitionally the same structure.
--     A GL frame has R transitive + converse WF → R is irreflexive (proved above).
--     A WFSPO has lt irreflexive + transitive + converse WF → it's a GL frame.
--     This means all of order theory applies to GL frames. -- !--

/-- **[P]roof**: Every GL frame is a well-founded strict partial order. -/
def GLFrame.toWFSPO (M : GLFrame) : WFSPO where
  carrier := M.W
  lt := M.R
  lt_irrefl := GLFrame.irrefl M
  lt_trans h1 h2 := M.R_trans h1 h2
  lt_wf := M.R_wf

/-- **[P]roof**: Every WFSPO is a GL frame. -/
def WFSPO.toGLFrame (S : WFSPO) : GLFrame where
  W := S.carrier
  R := S.lt
  R_trans h1 h2 := S.lt_trans h1 h2
  R_wf := S.lt_wf






-- !-- [B]oundary: Dense linear orders like (ℚ, <) do NOT give GL frames because
--     the converse relation (>) is not well-founded: the sequence 1, 1/2, 1/3, ...
--     is infinite strictly decreasing. GL frames correspond exactly to well-founded
--     partial orders, which excludes all dense orders and all infinite chains. -- !--

end GLPLogic


