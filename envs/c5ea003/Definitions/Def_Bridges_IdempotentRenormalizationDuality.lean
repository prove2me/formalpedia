-- Prove2me | Definitions.Def_Bridges_IdempotentRenormalizationDuality
-- name    : Bridges_IdempotentRenormalizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:35.964737+00:00
-- url     : https://prove2.me/theorems/f9a0454e-a825-450b-ae16-c1b06312835d
-- title:
--   Aether Catalog definitions — Bridges_IdempotentRenormalizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IdempotentRenormalizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IdempotentRenormalizationDuality.lean by skeleton subtraction
import Mathlib
/-
# Idempotent Renormalization Duality via Closure Scale Semimodules

This file formalizes a **certified equivalence between finite closure-theoretic
renormalization group data and idempotent semimodule transfer models**.

## Mathematical Dictionary

| Physics / RG concept          | Formal concept                              |
|-------------------------------|---------------------------------------------|
| Scale / energy level           | Element of a finite linear order `S`        |
| Configuration space            | Finite type `C`                              |
| Closure / coarse-graining      | Closure operator `cl : Finset C → Finset C` |
| RG flow map                    | Scale-transfer `ρ s t` for `s ≤ t`           |
| Observable at scale            | Section `σ : S → Finset C`                  |
| Admissible observable          | Closed + monotone section                    |
| Renormalized phase             | Extremal admissible section                  |
| Effective degrees of freedom   | Minimal generators of section lattice        |
| Bellman consistency            | Dynamic programming law on transfer data     |

## Main Results

* `monotone_endomap_eventually_stable` — Monotone extensive endo on finite set stabilizes
* `toTransferData_bellman` — RG data yields Bellman-consistent transfer
* `exists_extremal_decomposition` — Every admissible section decomposes into extremals
* `extremal_has_minimal_support` — Extremals have minimal support
* `exists_minimal_generator_family` — Minimal generators exist
* `reconstructClosure_stabilizes` — Iterated reconstruction stabilizes
* `idempotent_renormalization_duality` — Main theorem package
-/


set_option maxHeartbeats 800000

open Finset Function

noncomputable section

namespace IdempotentRenormalizationDuality

/-! ## §1. Closure Operators -/

/-- A closure operator on `Finset α`. -/
structure ClosureOp (α : Type*) [DecidableEq α] where
  cl : Finset α → Finset α
  extensive : ∀ s, s ⊆ cl s
  mono : ∀ {s t}, s ⊆ t → cl s ⊆ cl t
  idem : ∀ s, cl (cl s) = cl s

variable {α : Type*} [DecidableEq α]

def ClosureOp.IsClosed (C : ClosureOp α) (s : Finset α) : Prop := C.cl s = s


/-! ## §2. Scale-Indexed Closure Systems -/

/-- A finite scale-indexed closure system. -/
structure ScaleClosureSystem (S : Type*) (C : Type*) [Fintype S] [LinearOrder S]
    [DecidableEq S] [Fintype C] [DecidableEq C] where
  cl : S → ClosureOp C
  transfer : (s t : S) → s ≤ t → Finset C → Finset C
  transfer_mono : ∀ s t (h : s ≤ t) {a b : Finset C}, a ⊆ b →
    transfer s t h a ⊆ transfer s t h b
  transfer_id : ∀ s (h : s ≤ s) (a : Finset C), transfer s s h a = a
  transfer_comp : ∀ s t u (hst : s ≤ t) (htu : t ≤ u) (hsu : s ≤ u)
    (a : Finset C), transfer t u htu (transfer s t hst a) = transfer s u hsu a
  transfer_closure_compat : ∀ s t (h : s ≤ t) (a : Finset C),
    (cl s).IsClosed a → (cl t).IsClosed ((cl t).cl (transfer s t h a))
  transfer_empty : ∀ s t (h : s ≤ t), transfer s t h ∅ = ∅

variable {S C : Type*} [Fintype S] [LinearOrder S] [DecidableEq S]
  [Fintype C] [DecidableEq C]

/-! ## §3. Sections and Admissibility -/

abbrev Sect (S C : Type*) := S → Finset C

def Sect.bot : Sect S C := fun _ => ∅

instance : LE (Sect S C) := ⟨fun x y => ∀ s, x s ⊆ y s⟩

/-- A section is admissible if closed at each scale and monotone under transfer. -/
def ScaleClosureSystem.IsAdmissible (RG : ScaleClosureSystem S C) (x : Sect S C) : Prop :=
  (∀ s, (RG.cl s).IsClosed (x s)) ∧
  (∀ s t (h : s ≤ t), RG.transfer s t h (x s) ⊆ x t)


/-! ## §4. Extremal Sections -/

/-- A section is extremal: admissible, nonzero, join-irreducible. -/
def ScaleClosureSystem.IsExtremal (RG : ScaleClosureSystem S C) (e : Sect S C) : Prop :=
  RG.IsAdmissible e ∧ e ≠ Sect.bot ∧
  ∀ x y : Sect S C, RG.IsAdmissible x → RG.IsAdmissible y →
    (∀ s, e s ⊆ x s ∪ y s) → (∀ s, e s ⊆ x s) ∨ (∀ s, e s ⊆ y s)

/-- Scale support of a section. -/
def Sect.scaleSupport [Fintype S] (x : Sect S C) : Finset S :=
  Finset.univ.filter fun s => (x s).Nonempty

/-- Minimal support predicate: the scale support is the canonical support,
    and it is contained in the support of any admissible sub-section with
    equal pointwise closure (i.e., that generates the same closed data). -/
def ScaleClosureSystem.IsMinimalScaleSupport
    (RG : ScaleClosureSystem S C) (e : Sect S C) (supp : Finset S) : Prop :=
  supp = e.scaleSupport ∧
  ∀ x : Sect S C, RG.IsAdmissible x → (∀ s, e s ⊆ x s) →
    e.scaleSupport ⊆ x.scaleSupport

/-! ## §5. Monotone Endomorphism Stabilization (Lyapunov Principle) -/

/-
Any extensive endomorphism on finite subsets eventually stabilizes.
-/

/-! ## §6. Transfer Semimodule -/

/-- A transfer semimodule: scale-indexed values with compatible transfer maps. -/
structure TransferSemimodule (S : Type*) [Fintype S] [LinearOrder S] [DecidableEq S]
    (C : Type*) [DecidableEq C] [Fintype C] where
  value : S → Finset C
  transfer : (s t : S) → s ≤ t → Finset C → Finset C
  transfer_mono : ∀ s t (h : s ≤ t) {a b : Finset C}, a ⊆ b →
    transfer s t h a ⊆ transfer s t h b
  transfer_id : ∀ s (h : s ≤ s) v, transfer s s h v = v
  transfer_comp : ∀ s t u (hst : s ≤ t) (htu : t ≤ u) (hsu : s ≤ u) v,
    transfer t u htu (transfer s t hst v) = transfer s u hsu v

/-- Bellman consistency. -/
def TransferSemimodule.BellmanConsistent
    (T : TransferSemimodule S C) : Prop :=
  ∀ s t (h : s ≤ t), T.transfer s t h (T.value s) ⊆ T.value t

/-! ## §7. From RG Data to Transfer -/

def ScaleClosureSystem.toTransferData (RG : ScaleClosureSystem S C)
    (x : Sect S C) (_ : RG.IsAdmissible x) :
    TransferSemimodule S C where
  value := x
  transfer := RG.transfer
  transfer_mono := RG.transfer_mono
  transfer_id := RG.transfer_id
  transfer_comp := fun s t u hst htu hsu v => RG.transfer_comp s t u hst htu hsu v


/-! ## §8. Reconstruction Algorithm -/

structure PartialRGData (S C : Type*) [Fintype S] [LinearOrder S]
    [DecidableEq S] [Fintype C] [DecidableEq C] where
  current : Sect S C
  system : ScaleClosureSystem S C

/-- One reconstruction step: close + propagate transfers. -/
def reconstructStep (D : PartialRGData S C) : PartialRGData S C where
  current := fun s =>
    (D.system.cl s).cl (D.current s ∪
      Finset.univ.biUnion fun t =>
        if h : t ≤ s then D.system.transfer t s h (D.current t) else ∅)
  system := D.system

def reconstructIter : ℕ → PartialRGData S C → PartialRGData S C
  | 0, D => D
  | n + 1, D => reconstructStep (reconstructIter n D)


def totalEnergy (D : PartialRGData S C) : ℕ :=
  Finset.univ.sum fun s => (D.current s).card




/-! ## §9. Extremal Decomposition -/


/-! ## §10. Extremal Support -/

/-
Every extremal section has its canonical scale support as minimal support:
    any admissible section that pointwise contains e must be nonempty
    wherever e is nonempty.
-/

/-! ## §11. Minimal Generator Family -/

def ScaleClosureSystem.IsGeneratorFamily (RG : ScaleClosureSystem S C)
    (G : Finset (Sect S C)) : Prop :=
  (∀ g ∈ G, RG.IsAdmissible g) ∧
  ∀ x : Sect S C, RG.IsAdmissible x → x ≠ Sect.bot →
    ∃ H : Finset (Sect S C), H ⊆ G ∧ H.Nonempty ∧ ∀ s, x s = H.sup (· s)

def ScaleClosureSystem.IsMinimalGeneratorFamily (RG : ScaleClosureSystem S C)
    (G : Finset (Sect S C)) : Prop :=
  RG.IsGeneratorFamily G ∧
  ∀ G' : Finset (Sect S C), G' ⊂ G → ¬RG.IsGeneratorFamily G'


/-! ## §12. Bellman Reconstruction -/


/-! ## §13. Scale-Preserving Isomorphism -/

structure ScalePreservingIso (RG₁ RG₂ : ScaleClosureSystem S C) where
  toEquiv : C ≃ C
  closure_compat : ∀ s (a : Finset C),
    (RG₂.cl s).cl (a.map toEquiv.toEmbedding) =
    ((RG₁.cl s).cl a).map toEquiv.toEmbedding
  transfer_compat : ∀ s t (h : s ≤ t) (a : Finset C),
    RG₂.transfer s t h (a.map toEquiv.toEmbedding) =
    (RG₁.transfer s t h a).map toEquiv.toEmbedding


def ScaleClosureSystem.IsMinimalFlow (RG : ScaleClosureSystem S C) : Prop :=
  ∀ RG' : ScaleClosureSystem S C,
    (∀ s t (h : s ≤ t) v, RG'.transfer s t h v = RG.transfer s t h v) →
    (∀ s a, (RG'.cl s).IsClosed a → (RG.cl s).IsClosed a) →
    (∀ s a, (RG.cl s).IsClosed a → (RG'.cl s).IsClosed a)


/-! ## §14. Boundary Data -/

structure BoundaryData (S C : Type*) [Fintype S] [LinearOrder S]
    [DecidableEq S] [Fintype C] [DecidableEq C] where
  boundary_scales : Finset S
  observed : (s : S) → s ∈ boundary_scales → Finset C
  system : ScaleClosureSystem S C
  observed_closed : ∀ s (hs : s ∈ boundary_scales),
    (system.cl s).IsClosed (observed s hs)


/-! ## §15. Main Theorem Package -/


end IdempotentRenormalizationDuality


