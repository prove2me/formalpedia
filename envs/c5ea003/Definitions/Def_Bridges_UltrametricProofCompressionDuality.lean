-- Prove2me | Definitions.Def_Bridges_UltrametricProofCompressionDuality
-- name    : Bridges_UltrametricProofCompressionDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:56.213921+00:00
-- url     : https://prove2.me/theorems/37b329b6-8262-43f3-8f63-1a87270b09f7
-- title:
--   Aether Catalog definitions — Bridges_UltrametricProofCompressionDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricProofCompressionDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricProofCompressionDuality.lean by skeleton subtraction
import Mathlib
/-
# Ultrametric Proof Compression Duality via Observer Semimodules and
  Certified Minimal Refutation Reconstruction

This file formalizes a **finite algebraic realization theorem** for proof compression.
The main theorem establishes a canonical bijection between extremal observer classes
and minimal automaton states, analogous to Myhill–Nerode for proof compression.

## Bridges

- Ultrametric geometry ↔ Proof compression dynamics
- Prime congruence algebra ↔ Automata minimization (Myhill–Nerode)
- Observer separation ↔ Certified refutation reconstruction
-/


open Function Finset Classical

noncomputable section

/-! ## §1. Ultrametric Foundations -/

/-- An ultrametric distance predicate. -/
def UltraDistPred' {α : Type*} (d : α → α → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧
  (∀ x y, d x y = 0 ↔ x = y) ∧
  (∀ x y, d x y = d y x) ∧
  (∀ x y z, d x z ≤ max (d x y) (d y z))

/-! ## §2. Finite Compressed Proof System -/

/-- A finite compressed proof system with a combined transition `T = step ∘ compress`
and a refutation predicate. -/
structure FinCompProofSys (P : Type) [Fintype P] [DecidableEq P] where
  d : P → P → ℝ
  ultra : UltraDistPred' d
  T : P → P
  q : ℝ
  hq0 : 0 ≤ q
  hq1 : q < 1
  contractive : ∀ x y, d (T x) (T y) ≤ q * d x y
  refutes : P → Prop
  refDec : DecidablePred refutes

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ## §3. Behavioral Equivalence (Myhill–Nerode style) -/

/-- Two proof states are **behaviorally equivalent** if they agree on refutation
status at every future depth under the combined transition. -/
def behEquiv (S : FinCompProofSys P) (x y : P) : Prop :=
  ∀ n : ℕ, S.refutes (S.T^[n] x) ↔ S.refutes (S.T^[n] y)

theorem behEquiv_refl (S : FinCompProofSys P) (x : P) : behEquiv S x x :=
  fun _ => Iff.rfl

theorem behEquiv_symm (S : FinCompProofSys P) {x y : P}
    (h : behEquiv S x y) : behEquiv S y x :=
  fun n => (h n).symm

theorem behEquiv_trans (S : FinCompProofSys P) {x y z : P}
    (hxy : behEquiv S x y) (hyz : behEquiv S y z) : behEquiv S x z :=
  fun n => (hxy n).trans (hyz n)

/-- Behavioral equivalence as a `Setoid`. -/
def behSetoid (S : FinCompProofSys P) : Setoid P where
  r := behEquiv S
  iseqv := ⟨behEquiv_refl S, fun h => behEquiv_symm S h,
            fun h1 h2 => behEquiv_trans S h1 h2⟩

abbrev BehClass (S : FinCompProofSys P) := Quotient (behSetoid S)

/-- Behavioral equivalence is compatible with the transition T. -/
theorem behEquiv_T_compat (S : FinCompProofSys P) {x y : P}
    (h : behEquiv S x y) : behEquiv S (S.T x) (S.T y) := by
  intro n
  have := h (n + 1)
  rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this

/-- The transition T descends to the quotient. -/
def behTrans (S : FinCompProofSys P) : BehClass S → BehClass S :=
  Quotient.lift
    (fun x => @Quotient.mk _ (behSetoid S) (S.T x))
    (fun a b (h : behEquiv S a b) => Quotient.sound (behEquiv_T_compat S h))

/-- The refutation predicate descends to the quotient. -/
def behRefutes (S : FinCompProofSys P) : BehClass S → Prop :=
  Quotient.lift S.refutes
    (fun a b (h : behEquiv S a b) => propext (h 0))

/-! ## §4. Minimal Compressed Refutation Automaton -/

/-- A minimal compressed refutation automaton with surjective projection. -/
structure MinCompRefAut (P : Type) where
  State : Type
  instFin : Fintype State
  instDE : DecidableEq State
  trans : State → State
  proj : P → State
  proj_surj : Function.Surjective proj
  refPred : State → Prop

attribute [instance] MinCompRefAut.instFin
attribute [instance] MinCompRefAut.instDE

/-- The canonical minimal automaton from behavioral equivalence. -/
def MinAut (S : FinCompProofSys P) : MinCompRefAut P where
  State := BehClass S
  instFin := Quotient.fintype _
  instDE := Quotient.decidableEq
  trans := behTrans S
  proj x := @Quotient.mk _ (behSetoid S) x
  proj_surj := Quotient.mk_surjective
  refPred := behRefutes S

/-! ## §5. Observer Semimodule -/

structure ObsSemimod (P : Type) where
  Carrier : Type
  instFin : Fintype Carrier
  instDE : DecidableEq Carrier
  eval : Carrier → P → ℝ

attribute [instance] ObsSemimod.instFin
attribute [instance] ObsSemimod.instDE

/-- The canonical observer semimodule: indicator functions on behavioral classes. -/
def Obs (S : FinCompProofSys P) : ObsSemimod P where
  Carrier := BehClass S
  instFin := Quotient.fintype _
  instDE := Quotient.decidableEq
  eval cls x := if @Quotient.mk _ (behSetoid S) x = cls then 1 else 0



def ObsRealizCrit (O : ObsSemimod P) : Prop :=
  ∀ c : O.Carrier, ∃ x : P, O.eval c x ≠ 0

/-- Extraction by congruence quotient: the projection defines the same
partition as behavioral equivalence. -/
def ExtractedByCongQuot (S : FinCompProofSys P) (A : MinCompRefAut P) : Prop :=
  ∀ x y : P, A.proj x = A.proj y ↔ behEquiv S x y

/-- Reconstruction from observer: the projection defines the same partition
as observer agreement. -/
def ReconstructsFrom (O : ObsSemimod P) (A : MinCompRefAut P) : Prop :=
  ∀ x y : P, A.proj x = A.proj y ↔ ∀ c : O.Carrier, O.eval c x = O.eval c y

/-- Certified from distance data: behavioral equivalence is preserved by T. -/
def CertFromDist (S : FinCompProofSys P) (A : MinCompRefAut P) : Prop :=
  ∀ x y : P, A.proj x = A.proj y →
    ∀ n : ℕ, A.proj (S.T^[n] x) = A.proj (S.T^[n] y)

/-- Extremal ray class: a realized observer. -/
def ExtRayClass (O : ObsSemimod P) : Type :=
  { c : O.Carrier // ∃ x : P, O.eval c x ≠ 0 }

/-- Compressed state class: a reached automaton state. -/
def CompStateClass (A : MinCompRefAut P) : Type :=
  { s : A.State // ∃ x : P, A.proj x = s }

/-! ## §6. Core Lemmas -/













/-! ## §7. Extremal Ray–State Bijection -/


/-! ## §8. Helper: surjective maps with same kernel induce equiv on codomains -/

/-
If two surjective functions from P to finite types have the same kernel
(i.e. agree on which pairs map to the same element), their codomains are
in bijection.
-/

/-! ## §9. Uniqueness of Minimal Automaton -/


/-! ## §10. Main Duality Theorem -/


/-! ## §11. Reconstruction Converse -/

/-- The observer-equivalence relation induced by an observer semimodule. -/
def obsEquivOfSemimod (O : ObsSemimod P) (x y : P) : Prop :=
  ∀ c : O.Carrier, O.eval c x = O.eval c y

omit [Fintype P] [DecidableEq P] in
theorem obsEquivOfSemimod_equiv (O : ObsSemimod P) :
    Equivalence (obsEquivOfSemimod O) where
  refl _ _ := rfl
  symm h c := (h c).symm
  trans h1 h2 c := (h1 c).trans (h2 c)

def obsEquivOfSemimodSetoid (O : ObsSemimod P) : Setoid P where
  r := obsEquivOfSemimod O
  iseqv := obsEquivOfSemimod_equiv O

/-- Reconstruct an automaton from an observer semimodule. -/
def autFromObs (O : ObsSemimod P) : MinCompRefAut P where
  State := Quotient (obsEquivOfSemimodSetoid O)
  instFin := Quotient.fintype _
  instDE := Quotient.decidableEq
  trans := id  -- trivial transition (no dynamics required for reconstruction)
  proj := fun x => @Quotient.mk _ (obsEquivOfSemimodSetoid O) x
  proj_surj := Quotient.mk_surjective
  refPred := fun _ => False



end


