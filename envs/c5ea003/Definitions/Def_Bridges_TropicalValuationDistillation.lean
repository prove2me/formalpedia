-- Prove2me | Definitions.Def_Bridges_TropicalValuationDistillation
-- name    : Bridges_TropicalValuationDistillation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:05.751858+00:00
-- url     : https://prove2.me/theorems/67204f68-ec79-434a-9fa0-ae065f38888f
-- title:
--   Aether Catalog definitions — Bridges_TropicalValuationDistillation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalValuationDistillation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalValuationDistillation.lean by skeleton subtraction
import Mathlib
/-
# Tropical Valuation Distillation via Prime-Congruence Neural Sheaves
# and Certified Observer Compression

## Domain Bridge: Tropical Geometry ↔ Prime Congruence Spectra ↔ Certified ML Compression

The central bridge theorem:
> Observer compression is a sheaf over the prime congruence spectrum,
> and spectral separation certifies representation non-collision.

## Main Results (25+ theorems)

### Core Structures
* `ObserverFamily` — finite family of ring congruences as observers
* `PrimeCongruence` — prime-like ring congruences
* `CompressionStableCode` — codes stable under observer equivalence
* `ObserverStableScore` — score functions respecting observer equivalence
* `PosetPresheaf` — presheaf on a finite poset (finite spectral sheaf)

### Main Theorems
1. Valuation profile characterizes observer equivalence (`valProfile_eq_iff`)
2. Full separation implies profile injectivity (`valProfile_injective`)
3. Stalkwise separation implies global no-collision (`main_bridge_stalk`)
4. Stable codes factor through profiles (`stableCode_factors`)
5. Certified code separation on finsets (`certified_code_separation`)
6. Minimal codebook extraction (`codebook_extraction`)
7. Observer family refinement (`refinement_stable`, `refinement_sep`)
8. Score-based certified separation (`score_bridge`)
-/


open Finset Function

noncomputable section

namespace TropicalValuationDistillation

/-! ## §1. Observer Families and Observer Codes -/

/-- An observer family: a finite indexed family of ring congruences on `S`.
    Each congruence represents an observational channel that compresses elements
    into equivalence classes.
    Bridge: connects semiring congruence geometry to neural proof compression. -/
structure ObserverFamily (S : Type*) [Add S] [Mul S] where
  /-- Number of observers -/
  numObs : ℕ
  /-- The family of ring congruences -/
  obs : Fin numObs → RingCon S

/-- Observer equivalence: two elements are observer-equivalent if identified
    by every observer in the family. This is the kernel of joint observation. -/
def observerEquiv {S : Type*} [Add S] [Mul S] (F : ObserverFamily S)
    (x y : S) : Prop :=
  ∀ i : Fin F.numObs, (F.obs i) x y



/-- Full observer separation: every distinct pair is distinguished by some observer. -/
def FullySeparating {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) : Prop :=
  ∀ ⦃x y : S⦄, x ≠ y → ∃ i : Fin F.numObs, ¬(F.obs i) x y

/-- Observer separation on a finite subset. -/
def Separating {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) (T : Finset S) : Prop :=
  ∀ ⦃x y : S⦄, x ∈ T → y ∈ T → x ≠ y →
    ∃ i : Fin F.numObs, ¬(F.obs i) x y


/-! ## §2. Valuation Profile -/

/-- The observer code type: product of all quotient types.
    Bridge: the tropical feature space. -/
def ObsCode {S : Type*} [Add S] [Mul S] (F : ObserverFamily S) :=
  (i : Fin F.numObs) → (F.obs i).Quotient

/-- The valuation profile: sends each element to its tuple of quotient classes.
    Bridge: this is the tropical feature extractor. -/
def valProfile {S : Type*} [Add S] [Mul S] (F : ObserverFamily S)
    (x : S) : ObsCode F :=
  fun i => (F.obs i).toQuotient x

/-- **Profile Characterization Theorem**: Two elements have equal profiles iff
    they are observer-equivalent. This is the fundamental bridge between
    the algebraic (congruence) and the coding (profile) viewpoints. -/
theorem valProfile_eq_iff {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) (x y : S) :
    valProfile F x = valProfile F y ↔ observerEquiv F x y := by
  constructor
  · intro h i; exact (F.obs i).eq.mp (congr_fun h i)
  · intro h; funext i; exact (F.obs i).eq.mpr (h i)


/-- Profile is constant on observer equivalence classes. -/
theorem valProfile_constant {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) {x y : S} (h : observerEquiv F x y) :
    valProfile F x = valProfile F y :=
  (valProfile_eq_iff F x y).mpr h

/-! ## §3. Prime Congruences and Stalk Classes -/

/-- A prime congruence: a ring congruence with the prime property.
    Bridge: connects commutative algebra prime spectra to neural observation. -/
structure PrimeCongruence (S : Type*) [Add S] [Mul S] [Zero S] where
  /-- The underlying ring congruence -/
  con : RingCon S
  /-- Prime: if `con (a * b) 0` then `con a 0` or `con b 0` -/
  prime : ∀ a b : S, con (a * b) 0 → con a 0 ∨ con b 0

/-- The stalk valuation class at a prime congruence: records both the
    prime quotient class and the observer profile.
    Bridge: the local spectral data at a point of the prime spectrum. -/
def StalkClass {S : Type*} [Add S] [Mul S] [Zero S]
    (F : ObserverFamily S) (P : PrimeCongruence S) (x : S) :
    P.con.Quotient × ObsCode F :=
  (P.con.toQuotient x, valProfile F x)

/-! ## §4. Compression-Stable Codes -/

/-- A compression-stable code: respects observer equivalence.
    Bridge: models learned representations invariant under observational redundancy. -/
structure CompressionStableCode {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) (C : Type*) where
  /-- The encoding function -/
  encode : S → C
  /-- Stability: observer-equivalent elements get the same code -/
  stable : ∀ {x y : S}, observerEquiv F x y → encode x = encode y

/-- The canonical profile code is compression-stable. -/
def profileCode {S : Type*} [Add S] [Mul S] (F : ObserverFamily S) :
    CompressionStableCode F (ObsCode F) where
  encode := valProfile F
  stable := fun h => valProfile_constant F h

/-! ## §5. Core Separation Theorems -/





/-! ## §6. Separation Properties on Finite Sets -/





/-! ## §7. Diagonal Avoidance and Code Separation -/






/-! ## §8. Universal Property: Stable Codes Factor Through Profiles -/


/-! ## §9. Score Stability and Certified Margins -/

/-- A score function that respects observer equivalence.
    Bridge: models certified evaluation metrics in ML. -/
structure ObserverStableScore {S : Type*} [Add S] [Mul S]
    (F : ObserverFamily S) where
  score : S → ℕ
  stable : ∀ {x y : S}, observerEquiv F x y → score x = score y




/-! ## §10. Observer Family Operations -/

/-- Trivial observer family with zero observers. -/
def trivialFamily (S : Type*) [Add S] [Mul S] : ObserverFamily S where
  numObs := 0
  obs := Fin.elim0


/-- Single-observer family from one congruence. -/
def singleFamily {S : Type*} [Add S] [Mul S] (c : RingCon S) :
    ObserverFamily S where
  numObs := 1
  obs := ![c]



/-! ## §11. Refinement Properties -/



/-! ## §12. Certified Stratum Separation -/



/-! ## §13. Poset Presheaf (Finite Spectral Sheaf) -/

/-- A presheaf on a preorder: assigns a type to each point with restriction maps.
    Bridge: models spectral data that is locally compatible. -/
structure PosetPresheaf (P : Type*) [Preorder P] where
  /-- Object assignment -/
  obj : P → Type*
  /-- Restriction maps (contravariant) -/
  res : ∀ {p q : P}, p ≤ q → obj q → obj p
  /-- Restriction along reflexivity -/
  res_id : ∀ (p : P) (h : p ≤ p) (x : obj p), res h x = x
  /-- Restriction composes -/
  res_comp : ∀ {p q r : P} (hpq : p ≤ q) (hqr : q ≤ r) (x : obj r),
    res hpq (res hqr x) = res (le_trans hpq hqr) x

/-- A global section of a poset presheaf: a compatible family of local sections. -/
structure GlobalSection {P : Type*} [Preorder P] (F : PosetPresheaf P) where
  /-- Section at each point -/
  val : ∀ p : P, F.obj p
  /-- Compatibility with restrictions -/
  compatible : ∀ {p q : P} (h : p ≤ q), F.res h (val q) = val p

/-- The constant presheaf on a type `A`: assigns `A` everywhere with
    identity restrictions. -/
def constPresheaf (P : Type*) [Preorder P] (A : Type*) : PosetPresheaf P where
  obj _ := A
  res _ x := x
  res_id _ _ _ := rfl
  res_comp _ _ _ := rfl


/-! ## §14. Neural Sheaf Construction -/

/-- The neural sheaf stalk type at a prime congruence. -/
abbrev NeuralStalk {S : Type*} [Add S] [Mul S] [Zero S]
    (F : ObserverFamily S) (P : PrimeCongruence S) :=
  P.con.Quotient × ObsCode F

/-- Each element `x : S` defines a section of the neural sheaf:
    at each prime congruence, it gives a stalk valuation class. -/
def elementSection {S : Type*} [Add S] [Mul S] [Zero S]
    (F : ObserverFamily S) (x : S) (P : PrimeCongruence S) :
    NeuralStalk F P :=
  StalkClass F P x



/-! ## §15. Main Bridge Theorems -/




/-! ## §16. Bridge Connections -/






end TropicalValuationDistillation


