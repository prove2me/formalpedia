-- Prove2me | Definitions.Def_Logic_PosetTheory_BelnapBilattice
-- name    : Logic_PosetTheory_BelnapBilattice
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:13.867972+00:00
-- url     : https://prove2.me/theorems/b84eaeeb-60e0-4abc-819f-8cd10e1aa840
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_BelnapBilattice
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.BelnapBilattice`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/BelnapBilattice.lean by skeleton subtraction
import Mathlib
/-
  Belnap's FOUR₂ as a Distributive Bilattice

  We formalize Belnap's four-valued logic FOUR₂ and prove it carries the structure of
  a *distributive bilattice*: two bounded distributive lattice orderings (truth and
  knowledge) on the same four-element set, connected by a De Morgan negation that is
  an antitone involution in the truth ordering and a monotone lattice homomorphism in
  the knowledge ordering. We prove this negation is NOT a Boolean complement, which is
  the algebraic root of paraconsistency — the failure of "explosion" (ex falso quodlibet).

  ## Main Results

  1. `Belnap.instDistribLattice` — Truth ordering forms a bounded distributive lattice
  2. `Belnap.bneg_deMorgan_inf` / `bneg_deMorgan_sup` — De Morgan laws for Belnap negation
  3. `Belnap.bneg_not_complement` — Belnap negation violates non-contradiction (paraconsistency)
  4. `Belnap.explosion_fails` — Ex falso quodlibet fails
  5. `Belnap.kLE_distribLattice_axioms` — Knowledge ordering satisfies distributive lattice axioms
  6. `Belnap.bneg_antitone` — Negation is antitone in truth ordering
  7. `Belnap.bneg_kLE_monotone` — Negation is monotone in knowledge ordering
  8. `Belnap.bneg_k_homomorphism` — Negation is a knowledge-lattice homomorphism
  9. `consistent_consequence_nonmonotone` — Consistent credulous consequence is non-monotone

  ## References

  - Belnap, N. (1977). "A useful four-valued logic"
  - Fitting, M. (2002). "Bilattices and the Semantics of Logic Programming"
  - Arieli, O. & Avron, A. (1996). "Reasoning with logical bilattices"
-/

set_option autoImplicit false

/-! ## The Belnap Type -/

/-- The four truth values of Belnap's FOUR₂.
- `T` : true (true only)
- `F` : false (false only)
- `B` : both (true AND false — information glut)
- `N` : neither (neither true nor false — information gap) -/
inductive Belnap : Type
  | T : Belnap -- true
  | F : Belnap -- false
  | B : Belnap -- both true and false (glut)
  | N : Belnap -- neither true nor false (gap)
  deriving DecidableEq, Repr

namespace Belnap

instance : Fintype Belnap where
  elems := {T, F, B, N}
  complete := by rintro ⟨⟩ <;> simp

/-! ## Belnap Negation -/

/-- Belnap negation: swaps T↔F, fixes B and N.
This preserves information level but reverses truth polarity. -/
def bneg : Belnap → Belnap
  | T => F | F => T | B => B | N => N

/-! ## Truth Ordering

The truth ordering on FOUR₂ forms a diamond (M₂) lattice:
```
       T (top)
      / \
     B   N
      \ /
       F (bottom)
```
B and N are incomparable; F is the least element, T is the greatest.
-/

/-- Meet (conjunction) in the truth ordering. -/
def tInf : Belnap → Belnap → Belnap
  | T, T => T | T, F => F | T, B => B | T, N => N
  | F, T => F | F, F => F | F, B => F | F, N => F
  | B, T => B | B, F => F | B, B => B | B, N => F
  | N, T => N | N, F => F | N, B => F | N, N => N

/-- Join (disjunction) in the truth ordering. -/
def tSup : Belnap → Belnap → Belnap
  | T, T => T | T, F => T | T, B => T | T, N => T
  | F, T => T | F, F => F | F, B => B | F, N => N
  | B, T => T | B, F => B | B, B => B | B, N => T
  | N, T => T | N, F => N | N, B => T | N, N => N

/-! ## Truth Ordering: DistribLattice Instance -/

instance : LE Belnap where le a b := tInf a b = a

instance : DecidableRel (· ≤ · : Belnap → Belnap → Prop) :=
  fun a b => inferInstanceAs (Decidable (tInf a b = a))

instance : LT Belnap where lt a b := a ≤ b ∧ ¬b ≤ a

instance : Bot Belnap where bot := F
instance : Top Belnap where top := T

instance : BoundedOrder Belnap where
  bot_le := by decide
  le_top := by decide

-- !-- The truth ordering on FOUR₂ is the diamond lattice M₂, which is a bounded
-- distributive lattice. All axioms are verified by exhaustive case analysis
-- over the 4-element type. -- !--
instance : DistribLattice Belnap where
  sup := tSup
  inf := tInf
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  le_sup_inf := by decide

/-! ## Negation Properties in Truth Ordering -/


-- !-- De Morgan's laws hold for Belnap negation with respect to the truth ordering.
-- This is proved by exhaustive case analysis on the 4×4 cases. -- !--



-- !-- The central paraconsistency result: Belnap negation is NOT a lattice complement.
-- In a Boolean algebra, a ⊓ compl a = ⊥ for all a. Here, B ⊓ bneg B = B ⊓ B = B ≠ F = ⊥.
-- This is the algebraic root of paraconsistency. -- !--




/-! ## Knowledge Ordering

The knowledge ordering on FOUR₂ also forms a diamond lattice, but rotated 90°:
```
       B (top — maximal information)
      / \
     T   F
      \ /
       N (bottom — no information)
```
T and F are incomparable in the knowledge ordering.
-/

/-- Meet (consensus) in the knowledge ordering. -/
def kInf : Belnap → Belnap → Belnap
  | T, T => T | T, F => N | T, B => T | T, N => N
  | F, T => N | F, F => F | F, B => F | F, N => N
  | B, T => T | B, F => F | B, B => B | B, N => N
  | N, T => N | N, F => N | N, B => N | N, N => N

/-- Join (gullibility) in the knowledge ordering. -/
def kSup : Belnap → Belnap → Belnap
  | T, T => T | T, F => B | T, B => B | T, N => T
  | F, T => B | F, F => F | F, B => B | F, N => F
  | B, T => B | B, F => B | B, B => B | B, N => B
  | N, T => T | N, F => F | N, B => B | N, N => N

/-- The knowledge ordering: N ≤ₖ T, N ≤ₖ F, T ≤ₖ B, F ≤ₖ B. -/
def kLE (a b : Belnap) : Prop := kInf a b = a

instance kLE_decidable : DecidableRel kLE :=
  fun a b => inferInstanceAs (Decidable (kInf a b = a))

/-! ## Knowledge Ordering: Distributive Lattice Axioms -/

-- !-- The knowledge ordering also forms a bounded distributive lattice, with N as bottom
-- and B as top. This gives FOUR₂ its bilattice structure: two independent lattice
-- orderings on the same set. Proved by exhaustive case analysis. -- !--













/-! ## Bilattice Structure: Negation and Knowledge Ordering -/

-- !-- Negation is MONOTONE in the knowledge ordering (unlike truth ordering where it's
-- antitone). This is the key bilattice interaction: negation reverses one ordering
-- but preserves the other. Moreover, negation is a lattice HOMOMORPHISM for the
-- knowledge ordering (preserving both meet and join). -- !--




/-! ## Independence of the Two Orderings -/


/-! ## Interlacing: Truth Operations Distribute over Knowledge Operations -/

-- !-- FOUR₂ is an INTERLACED bilattice: the truth meet and join are monotone with
-- respect to the knowledge ordering. This means truth operations preserve
-- information content. Proved by 64-case exhaustion. -- !--



end Belnap

/-! ## Non-Monotonicity of Consistent Credulous Consequence -/

section NonMonotonicity

variable {α : Type}

/-- A Belnap valuation is consistent if it never assigns "both" (B). -/
def BelnapConsistent (v : α → Belnap) : Prop := ∀ x, v x ≠ Belnap.B

/-- A valuation satisfies a set of constraints if it agrees on all entries. -/
def BelnapSatisfies (v : α → Belnap) (kb : Set (α × Belnap)) : Prop :=
  ∀ p ∈ kb, v p.1 = p.2

/-- Consistent credulous consequence: variable x is "true" under some consistent
    valuation that satisfies the knowledge base. In a consistent valuation,
    "designated" reduces to v x = T (since B is excluded). -/
def ConsistentCredulousTruth (kb : Set (α × Belnap)) (x : α) : Prop :=
  ∃ v : α → Belnap, BelnapConsistent v ∧ BelnapSatisfies v kb ∧ v x = Belnap.T

-- !-- Consistent credulous consequence is non-monotone: adding information to a
-- knowledge base can invalidate previously derivable conclusions. The witness
-- uses Unit (single variable): kb₁ = {((), T)} has a consistent model (v _ = T),
-- but kb₂ = {((), T), ((), F)} is unsatisfiable (v () = T and v () = F
-- simultaneously is impossible). -- !--


end NonMonotonicity


