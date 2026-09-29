-- Prove2me | Definitions.Def_Bridges_ClosureRateDistortionDuality
-- name    : Bridges_ClosureRateDistortionDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:35.597712+00:00
-- url     : https://prove2.me/theorems/b29074c9-28f6-4baf-a8e9-95bfe6a6bb88
-- title:
--   Aether Catalog definitions — Bridges_ClosureRateDistortionDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureRateDistortionDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureRateDistortionDuality.lean by skeleton subtraction
import Mathlib
/-
# Tropical Rate–Distortion Duality via Idempotent Information Semimodules

This file formalizes a duality between finite closure-information systems and
tropical rate–distortion profiles, yielding certified minimal quantizer
reconstruction from closure capacity data.

## Main results

- `closureCapacity_class_invariant` — Capacity is constant on closure classes.
- `closure_to_tropical_profile` — Unique tropical profile from closure capacity.
- `rdProfile_top_eq_zero` — RD profile at ⊤ is 0.
- `quantizerEquiv_distortion_eq` — Equivalent quantizers have same distortion.
- `closure_rd_duality_summary` — Main duality theorem.
- `tropical_semimodule_laws` — Min-plus semimodule axioms.
- `tropicalLegendre_antitone` — Tropical Legendre transform is antitone.
- `closure_morphism_contracts` — Data processing inequality.
- `ultraDist_triangle` — Ultrametric triangle inequality.

## Bridges

- **Closure Theory ↔ Lossy Compression**: Closure atoms = optimal codebook cells.
- **Tropical Algebra ↔ Information Theory**: Min-plus operations = rate–distortion.
- **Lattice Theory ↔ Quantization**: Join-irreducible elements = irreducible cells.
-/


open Set Classical

noncomputable section

namespace Bridges.AlgebraEMLTropical.ClosureRateDistortionDuality

/-! ## §1. Closure Operator -/

/-- A closure operator on `Set α`: monotone, extensive, idempotent. -/
structure IsClosureOp {α : Type*} (cl : Set α → Set α) : Prop where
  idempotent : ∀ s, cl (cl s) = cl s
  monotone : ∀ ⦃s t : Set α⦄, s ⊆ t → cl s ⊆ cl t
  extensive : ∀ s, s ⊆ cl s

/-- A set is closed under `cl`. -/
def IsClsd {α : Type*} (cl : Set α → Set α) (s : Set α) : Prop := cl s = s


/-! ## §2. Closure Capacity -/

/-- A normalized, monotone, closure-invariant function to `WithTop ℕ`,
satisfying the ultrametric join inequality. -/
structure ClCap (α : Type*) [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) where
  val : Set α → WithTop ℕ
  closed_inv : ∀ s : Set α, val (cl s) = val s
  mono : ∀ ⦃s t : Set α⦄, s ⊆ t → val s ≤ val t
  norm_bot : val ∅ = 0
  ultra_join : ∀ s t : Set α, val (cl (s ∪ t)) ≤ max (val s) (val t)



/-! ## §3. Separation Axiom -/

/-- The closure system separates points. -/
def IsSeparated {α : Type*} (cl : Set α → Set α) : Prop :=
  ∀ a b : α, cl {a} = cl {b} → a = b

/-! ## §4. Closure Equivalence -/

def clEquiv {α : Type*} (cl : Set α → Set α) (a b : α) : Prop := cl {a} = cl {b}



/-! ## §5. Quantizer -/

/-- A quantizer partitions `α` into `k` closure-stable cells. -/
structure Quantizer (α : Type*) [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) (k : ℕ) where
  assign : α → Fin k
  cells_closed : ∀ i : Fin k, IsClsd cl {x : α | assign x = i}
  cells_nonempty : ∀ i : Fin k, ∃ a : α, assign a = i

/-- The cell of a quantizer containing element `a`. -/
def Quantizer.cell {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} {k : ℕ} (q : Quantizer α cl k) (a : α) : Set α :=
  {x : α | q.assign x = q.assign a}


/-! ## §6. Distortion -/

/-- Maximum within-cell distortion. -/
def quantizerDist {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} {k : ℕ}
    (d : α → α → WithTop ℕ) (q : Quantizer α cl k) : WithTop ℕ :=
  Finset.univ.sup fun a => Finset.univ.sup fun b =>
    if q.assign a = q.assign b then d a b else 0

/-! ## §7. Quantizer Equivalence -/

/-- Two quantizers are equivalent via a bijection on cells. -/
def QEquiv {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} {k k' : ℕ}
    (q : Quantizer α cl k) (q' : Quantizer α cl k') : Prop :=
  ∃ σ : Fin k → Fin k', Function.Bijective σ ∧
    ∀ a : α, σ (q.assign a) = q'.assign a


/-
Equivalent quantizers have the same distortion.
-/


/-! ## §8. Tropical Min-Plus Algebra -/

/-- Tropical addition = min. -/
def tAdd (a b : WithTop ℕ) : WithTop ℕ := min a b

/-- Tropical multiplication = plus. -/
def tMul (a b : WithTop ℕ) : WithTop ℕ := a + b











/-! ## §9. Tropical Distortion Vectors -/

/-- Componentwise tropical addition (min). -/
def tdvAdd {k : ℕ} (v w : Fin k → WithTop ℕ) : Fin k → WithTop ℕ :=
  fun i => min (v i) (w i)





/-! ## §10. Closure-Induced Distortion -/

/-- The distortion induced by a closure capacity: `d(a, b) = v({a, b})`. -/
def clDist {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} (v : ClCap α cl) (a b : α) : WithTop ℕ :=
  v.val {a, b}


/-! ## §11. Rate–Distortion Profile -/

/-- The RD profile: number of generators exceeding the distortion threshold. -/
def rdProfile {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α}
    (v : ClCap α cl) (D : WithTop ℕ) : ℕ :=
  Finset.card (Finset.univ.filter fun a => D < v.val {a})


/-
The RD profile is antitone: higher distortion ⟹ fewer generators exceed it.
-/


/-! ## §12. Capacity Union Bound -/



/-! ## §13. Tropical Legendre Transform -/

/-- The tropical Legendre transform of a capacity function. -/
def tropLegendre {α : Type*} [Fintype α] [DecidableEq α]
    (C : Set α → WithTop ℕ) (D : WithTop ℕ) : WithTop ℕ :=
  ⨅ (s : Set α) (_ : C s ≤ D), C s


/-! ## §14. Tropical Pairing -/

/-- Tropical inner product: min over i of (c_i + d_i). -/
def tropPairing {k : ℕ} (c d : Fin k → WithTop ℕ) : WithTop ℕ :=
  Finset.univ.inf fun i => c i + d i


/-! ## §15. Generator Theorem -/

/-- Generator values: capacity on singletons. -/
def generators {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} (v : ClCap α cl) (a : α) : WithTop ℕ :=
  v.val {a}


/-! ## §16. Forward Direction of Duality -/


/-! ## §17. Cell Capacity Bound -/


/-! ## §18. Closure Atom Structure -/

/-- A closed set is an atom: nonempty with no proper nonempty closed subsets. -/
def IsAtom' {α : Type*} (cl : Set α → Set α) (s : Set α) : Prop :=
  IsClsd cl s ∧ s.Nonempty ∧
  ∀ t : Set α, IsClsd cl t → t ⊆ s → t.Nonempty → t = s


/-! ## §19. Feasible Rates -/

/-- The set of feasible quantizer sizes at distortion level D. -/
def feasRates {α : Type*} [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) (d : α → α → WithTop ℕ) (D : WithTop ℕ) : Set ℕ :=
  {k : ℕ | ∃ q : Quantizer α cl k, quantizerDist d q ≤ D}


/-! ## §20. Concrete Examples -/

/-- Identity closure operator. -/
def idCl (α : Type*) : Set α → Set α := id


/-- Zero capacity: everything has cost 0. -/
def zeroCap {α : Type*} [Fintype α] [DecidableEq α]
    (cl : Set α → Set α) : ClCap α cl where
  val _ := 0
  closed_inv _ := rfl
  mono _ _ _ := le_refl _
  norm_bot := rfl
  ultra_join _ _ := by simp




/-! ## §21. Ultrametric Information Distance -/

/-- Ultrametric pseudo-distance: `d(s,t) = v(cl(s ∪ t))`. -/
def ultraDist {α : Type*} [Fintype α] [DecidableEq α]
    {cl : Set α → Set α} (v : ClCap α cl) (s t : Set α) : WithTop ℕ :=
  v.val (cl (s ∪ t))


/-
The ultrametric strong triangle inequality.
-/

/-! ## §22. Capacity Bounded by Closure Containment -/


/-! ## §23. Capacity Table and Optimal Cell Count -/

/-- A capacity table: generator values on each element. -/
structure CapTable (α : Type*) [Fintype α] [DecidableEq α] where
  gen : α → WithTop ℕ

/-- Optimal cell count at distortion threshold D. -/
def optCells {α : Type*} [Fintype α] [DecidableEq α]
    (tab : CapTable α) (D : WithTop ℕ) : ℕ :=
  Finset.card (Finset.univ.filter fun a => D < tab.gen a)


/-
Optimal cell count is antitone.
-/

/-! ## §24. Main Duality Summary -/


/-! ## §25. Information Contraction (Data Processing Inequality) -/

/-
**Theorem**: Closure morphisms contract information.
A closure morphism `f : α → β` (with `f '' (clα s) ⊆ clβ (f '' s)`) induces
a pullback capacity that is no larger than the original.
-/



/-- **Theorem**: Equivalence of unit shift is reflexive. -/
def EquivUpToShift {α : Type*}
    (f g : Set α → WithTop ℕ) : Prop :=
  ∃ c : ℕ, ∀ s, g s = f s + ↑c


/-
**Theorem**: Two capacities agreeing on singletons agree on all sets
(via closure invariance).
-/

end Bridges.AlgebraEMLTropical.ClosureRateDistortionDuality


