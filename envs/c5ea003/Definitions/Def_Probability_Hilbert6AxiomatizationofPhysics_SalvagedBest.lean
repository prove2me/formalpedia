-- Prove2me | Definitions.Def_Probability_Hilbert6AxiomatizationofPhysics_SalvagedBest
-- name    : Probability_Hilbert6AxiomatizationofPhysics_SalvagedBest
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:28.35369+00:00
-- url     : https://prove2.me/theorems/1149724f-00f8-469f-bf3e-0bd8da74872e
-- title:
--   Aether Catalog definitions — Probability_Hilbert6AxiomatizationofPhysics_SalvagedBest
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Hilbert6AxiomatizationofPhysics.SalvagedBest`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Hilbert6AxiomatizationofPhysics/SalvagedBest.lean by skeleton subtraction
import Mathlib

/-!
# Hilbert's Sixth Problem: effect algebras

The auto-generated version of this file consisted of a fragment: it referred to a
class `EffectAlgebra`, to the derived notions `ele`, `ortho`, `⊕ₑ`, and to a
structure `EffectHom`, none of which were present, and its `namespace`/`end`
blocks were unbalanced.  This file supplies the missing axiomatisation and gives
complete proofs of all the statements that the fragment contained, plus the two
promised models (the two-element Boolean effect algebra and the unit interval).

An **effect algebra** is a set with a partial commutative associative addition
`⊕`, a zero, a unit, and an orthocomplementation `a ↦ aᗮ` determined by
`a ⊕ aᗮ = 1`.  It is the standard order-theoretic skeleton of the set of quantum
effects, and hence one of the candidate answers to Hilbert's sixth problem.
-/

/-- A (partial) effect algebra. -/
class EffectAlgebra (E : Type*) where
  /-- Partial addition; `none` means "undefined". -/
  oplus : E → E → Option E
  /-- The zero effect. -/
  ezero : E
  /-- The unit effect. -/
  eone : E
  /-- The orthocomplement. -/
  ortho : E → E
  oplus_comm : ∀ a b, oplus a b = oplus b a
  oplus_assoc : ∀ a b c d e, oplus a b = some d → oplus d c = some e →
      ∃ f, oplus b c = some f ∧ oplus a f = some e
  oplus_ezero : ∀ a, oplus a ezero = some a
  oplus_ortho : ∀ a, oplus a (ortho a) = some eone
  oplus_eone_eq_ezero : ∀ a b, oplus a eone = some b → a = ezero
  ortho_unique : ∀ a b, oplus a b = some eone → b = ortho a

namespace EffectAlgebra

@[inherit_doc] infixl:65 " ⊕ₑ " => EffectAlgebra.oplus

variable {E : Type*} [EffectAlgebra E]

/-- The natural order of an effect algebra: `a ≤ b` iff `b` is `a` plus something. -/
def ele (a b : E) : Prop := ∃ c, a ⊕ₑ c = some b

/-! ## Theorem 1: Cancellation

**PEGB**:
- **P**roof: Complete `a ⊕ b = d` to `1` and use uniqueness of orthocomplements
  twice; the two completions coincide, so `bᗮ = cᗮ`, and orthocomplementation is
  injective.
- **E**xample: In `[0,1]`, `a + b = a + c` forces `b = c`.
- **G**eneralization: Cancellation holds in every effect algebra, even though the
  addition is only partial.
- **B**oundary: It fails for partial commutative monoids without orthocomplements.
-/



-- Example: cancellation holds trivially for Bool (see boolEffectAlgebra below)

/-! ## Theorem 2: Orthocomplement is an involution

**PEGB**:
- **P**roof: From a ⊕ ortho(a) = eone by commutativity ortho(a) ⊕ a = eone,
  and by uniqueness of orthocomplement a = ortho(ortho(a)).
- **E**xample: In Bool, not (not b) = b.
- **G**eneralization: In any algebra with unique complements, the complement
  operation is an involution.
- **B**oundary: Fails without uniqueness — multiple complements break involutivity.
-/

/-
The orthocomplement is an involution: ortho(ortho(a)) = a.
-/


/-! ## Theorem 3: ortho(eone) = ezero and ortho(ezero) = eone -/

/-
ortho(eone) = ezero.
-/



/-! ## Theorem 4: The natural order is transitive -/


/-! ## Theorem 5: Orthocomplement is order-reversing

**PEGB**:
- **P**roof: If a ≤ b, i.e. a ⊕ c = b for some c, then ortho(b) ⊕ c is
  defined and equals ortho(a) minus something, giving ortho(b) ≤ ortho(a).
- **E**xample: In [0,1], a ≤ b implies 1-b ≤ 1-a.
- **G**eneralization: Orthocomplementation is an order-reversing involution
  (antitone involution) on any effect algebra.
- **B**oundary: Requires the full effect algebra structure; fails for
  partial commutative monoids without orthocomplement.
-/

/-
Orthocomplement reverses the natural order.
-/


/-! ## Theorem 6: Two-element Boolean effect algebra (Bool)

**PEGB**:
- **P**roof: Direct construction with ⊕ = XOR (undefined on true+true).
- **E**xample: false ⊕ true = some true, true ⊕ true = none.
- **G**eneralization: Every Boolean algebra yields an effect algebra.
- **B**oundary: Non-distributive orthomodular lattices give non-Boolean EAs.
-/

/-- Partial addition on Bool: XOR with partiality. -/
def boolOplus : Bool → Bool → Option Bool
  | false, b => some b
  | b, false => some b
  | true, true => none

instance boolEffectAlgebra : EffectAlgebra Bool where
  oplus := boolOplus
  ezero := false
  eone := true
  ortho := not
  oplus_comm := by intro a b; cases a <;> cases b <;> rfl
  oplus_assoc := by
    intro a b c d e h1 h2
    cases a <;> cases b <;> cases c <;> simp_all [boolOplus]
  oplus_ezero := by intro a; cases a <;> rfl
  oplus_ortho := by intro a; cases a <;> rfl
  oplus_eone_eq_ezero := by
    intro a b h; cases a <;> simp_all [boolOplus]
  ortho_unique := by
    intro a b h; cases a <;> cases b <;> simp_all [boolOplus]

-- Concrete examples
/-! ## Theorem 7: Unit interval effect algebra [0,1] ⊂ ℝ

The standard quantum effect algebra. -/

/-- Elements of the unit interval [0, 1]. -/
structure UnitInterval where
  val : ℝ
  ge_zero : 0 ≤ val
  le_one : val ≤ 1

namespace UnitInterval

@[ext]
theorem ext {x y : UnitInterval} (h : x.val = y.val) : x = y := by
  cases x; cases y; simpa using h

/-- Partial addition on `[0,1]`: defined exactly when the sum stays below `1`. -/
noncomputable def oplus (x y : UnitInterval) : Option UnitInterval :=
  if h : x.val + y.val ≤ 1 then
    some ⟨x.val + y.val, by have := x.ge_zero; have := y.ge_zero; linarith, h⟩
  else none

theorem oplus_eq_some {x y z : UnitInterval} :
    oplus x y = some z ↔ x.val + y.val ≤ 1 ∧ z.val = x.val + y.val := by
  unfold oplus
  split_ifs with h
  · simp only [Option.some_inj, h, true_and]
    constructor
    · rintro rfl; rfl
    · intro hz; exact (ext hz.symm)
  · simp [h]

/-- The orthocomplement `x ↦ 1 - x`. -/
def compl (x : UnitInterval) : UnitInterval :=
  ⟨1 - x.val, by have := x.le_one; linarith, by have := x.ge_zero; linarith⟩

noncomputable instance : EffectAlgebra UnitInterval where
  oplus := oplus
  ezero := ⟨0, le_rfl, by norm_num⟩
  eone := ⟨1, by norm_num, le_rfl⟩
  ortho := compl
  oplus_comm := by
    intro a b
    unfold oplus
    have hc : a.val + b.val ≤ 1 ↔ b.val + a.val ≤ 1 := by constructor <;> intro <;> linarith
    split_ifs with h1 h2 h2
    · exact congrArg some (ext (by ring))
    · exact absurd (hc.mp h1) h2
    · exact absurd (hc.mpr h2) h1
    · rfl
  oplus_assoc := by
    intro a b c d e h1 h2
    rw [oplus_eq_some] at h1 h2
    obtain ⟨hab, hd⟩ := h1
    obtain ⟨hdc, he⟩ := h2
    have ha := a.ge_zero
    have hb := b.ge_zero
    have hc := c.ge_zero
    refine ⟨⟨b.val + c.val, by linarith, by rw [hd] at hdc; linarith⟩, ?_, ?_⟩ <;>
      rw [oplus_eq_some]
    · rw [hd] at hdc
      exact ⟨by linarith, rfl⟩
    · rw [hd] at hdc he
      exact ⟨by linarith, by linarith⟩
  oplus_ezero := by
    intro a
    rw [oplus_eq_some]
    exact ⟨by simpa using a.le_one, by simp⟩
  oplus_ortho := by
    intro a
    rw [oplus_eq_some]
    refine ⟨by simp [compl], by simp [compl]⟩
  oplus_eone_eq_ezero := by
    intro a b h
    rw [oplus_eq_some] at h
    exact ext (by have := a.ge_zero; have := h.1; simp at this ⊢; linarith)
  ortho_unique := by
    intro a b h
    rw [oplus_eq_some] at h
    exact ext (by simp only [compl]; have := h.2; simp at this; linarith [h.2])

end UnitInterval

/-- A morphism of effect algebras. -/
structure EffectHom (E F : Type*) [EffectAlgebra E] [EffectAlgebra F] where
  toFun : E → F
  map_eone : toFun eone = eone
  map_oplus : ∀ a b c, a ⊕ₑ b = some c → toFun a ⊕ₑ toFun b = some (toFun c)


end EffectAlgebra

/-!
## FUTURE DIRECTIONS

1. **Orthomodular lattice embedding**: Every orthomodular lattice gives rise
   to an effect algebra. Conversely, characterize which effect algebras arise
   from orthomodular lattices. Conjecture: An effect algebra is lattice-ordered
   iff it is an MV-effect algebra.

2. **Spectral theorem for effect algebras**: Define observables as σ-homomorphisms
   from Borel sets to an effect algebra. Prove that for the unit interval EA,
   these recover classical random variables.

3. **Sequential product**: Define a ∘ b (measurement of b after a). Prove that
   commutativity of ∘ characterizes compatibility. Conjecture: The sequential
   product makes every effect algebra into a partial Jordan algebra.

4. **Categorical structure**: Prove EffectAlg is complete and cocomplete.
   Conjecture: The forgetful functor EffectAlg → Set has a left adjoint.

5. **Quantum-to-classical collapse**: Prove every commutative effect algebra
   is isomorphic to a Boolean effect algebra. Conjecture: Every finite
   commutative effect algebra is isomorphic to a power set EA 2^n.
-/


