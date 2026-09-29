-- Prove2me | Definitions.Def_Bridges_TropicalLensBerggrenDuality
-- name    : Bridges_TropicalLensBerggrenDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:32.707702+00:00
-- url     : https://prove2.me/theorems/91df5ef6-a7ca-4167-8382-ecfe203bfcd1
-- title:
--   Aether Catalog definitions — Bridges_TropicalLensBerggrenDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalLensBerggrenDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalLensBerggrenDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Lens–Berggren Duality

## Geodesic Semimodules, Certified Finite Realization, and Factor Reconstruction
## via Inverse Tropical Geometry on Arithmetic Trees

This module establishes a formal bridge connecting:
- **Min-plus (tropical) algebra** on arrival profiles
- **Berggren tree arithmetic dynamics** (primitive Pythagorean triple generation)
- **Inverse-problem realization** (reconstructing sources from observed delays)
- **Certified factor reconstruction** from geometric delay data

### Main Theorems

1. `berggren_tropical_lens_reconstruction`: Certified reconstruction uniqueness.
2. `finite_berggren_delay_congruence`: The bounded observational quotient is finite.
3. `semiprime_delay_profile_injective`: Separated delay spectra distinguish factor data.
4. `directObs_transform_eq`: Direct-observation systems faithfully read sources.
5. `directObs_separation`: Direct-observation systems are delay-separated.
6. `berggren_tropical_lens_duality`: Complete duality theorem.

### Keywords
tropical arithmetic lensing, Berggren tree, min-plus geodesic, finite realization,
minimal systems, arithmetic tomography, factor reconstruction, semiprime detection,
certified sensing, Myhill–Nerode, idempotent analysis
-/

open Finset BigOperators Function

noncomputable section

namespace BerggrenTropicalLens

-- ═══════════════════════════════════════════════════════════════════════════════
-- §1. MIN-PLUS TROPICAL FOUNDATIONS
-- ═══════════════════════════════════════════════════════════════════════════════



-- ═══════════════════════════════════════════════════════════════════════════════
-- §2. BERGGREN LENS SYSTEM
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A Berggren Lens System models tropical gravitational lensing on an
    arithmetic graph with finite node set, source weights, observers,
    and min-plus edge costs. -/
structure BerggrenLensSystem where
  Node : Type
  [instFintype : Fintype Node]
  [instDecEq : DecidableEq Node]
  [instNonempty : Nonempty Node]
  source : Node → ℕ
  observers : Finset Node
  obs_nonempty : observers.Nonempty
  edgeCost : Node → Node → ℕ

attribute [instance] BerggrenLensSystem.instFintype BerggrenLensSystem.instDecEq
  BerggrenLensSystem.instNonempty

abbrev BerggrenSource (Sys : BerggrenLensSystem) := Sys.Node → ℕ

-- ═══════════════════════════════════════════════════════════════════════════════
-- §3. TROPICAL LENS TRANSFORM
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The tropical lens transform: min-plus convolution.
    `lensTransform Sys S o = min_s (S(s) + edgeCost(s, o))` -/
def lensTransform (Sys : BerggrenLensSystem) (S : BerggrenSource Sys)
    (o : Sys.Node) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun s => S s + Sys.edgeCost s o)

def BerggrenLensSystem.delayProfile (Sys : BerggrenLensSystem) :
    Sys.Node → ℕ := lensTransform Sys Sys.source

-- ═══════════════════════════════════════════════════════════════════════════════
-- §4. OBSERVATIONAL EQUIVALENCE
-- ═══════════════════════════════════════════════════════════════════════════════

def ObservationallyEquivalent (Sys : BerggrenLensSystem)
    (S T : BerggrenSource Sys) : Prop :=
  ∀ o ∈ Sys.observers, lensTransform Sys S o = lensTransform Sys T o





-- ═══════════════════════════════════════════════════════════════════════════════
-- §5. DELAY SEPARATION
-- ═══════════════════════════════════════════════════════════════════════════════

def BerggrenLensSystem.DelaySeparated (Sys : BerggrenLensSystem) : Prop :=
  ∀ S T : BerggrenSource Sys,
    (∀ o ∈ Sys.observers, lensTransform Sys S o = lensTransform Sys T o) →
    ObservationallyEquivalent Sys S T

/-
═══════════════════════════════════════════════════════════════════════════════
§6. LENS TRANSFORM PROPERTIES
═══════════════════════════════════════════════════════════════════════════════

The lens transform is monotone in the source weighting.
-/

/-
The lens transform at o is ≤ S(o) + edgeCost(o, o).
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- §7. TROPICAL LENS REALIZATION
-- ═══════════════════════════════════════════════════════════════════════════════

structure TropicalLensRealization (Sys : BerggrenLensSystem) where
  realSource : BerggrenSource Sys
  activeNodes : Finset Sys.Node

def TropicalLensRealization.Realizes {Sys : BerggrenLensSystem}
    (R : TropicalLensRealization Sys) (profile : Sys.Node → ℕ) : Prop :=
  ∀ o ∈ Sys.observers, lensTransform Sys R.realSource o = profile o


/-
═══════════════════════════════════════════════════════════════════════════════
§8. RECONSTRUCTION AND REALIZATION THEOREMS
═══════════════════════════════════════════════════════════════════════════════

**Berggren Tropical Lens Reconstruction.**
    Under delay separation, any source producing the same delay profile
    as the original is observationally equivalent to it.
-/

/-
**Berggren Tropical Lens Finite Realization.**
    The system's own source provides a canonical realization.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- §9. FINITE CONGRUENCE ON BOUNDED SOURCES
-- ═══════════════════════════════════════════════════════════════════════════════


/-
**Finite Berggren Delay Congruence.**
    The number of distinct delay profiles achievable by B-bounded sources
    is finite (bounded by (B+1)^|Node|).
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- §10. SEMIPRIME-ENCODED SOURCES
-- ═══════════════════════════════════════════════════════════════════════════════




/-- An encoding mapping factor data to sources, injective on delay profiles. -/
structure FactorSensitiveEncoding (Sys : BerggrenLensSystem) where
  encode : (p : ℕ) → (q : ℕ) → 2 ≤ p → 2 ≤ q → BerggrenSource Sys
  injective_on_delays :
    ∀ p₁ q₁ p₂ q₂ : ℕ,
    ∀ (hp₁ : 2 ≤ p₁) (hq₁ : 2 ≤ q₁) (hp₂ : 2 ≤ p₂) (hq₂ : 2 ≤ q₂),
    (∀ o ∈ Sys.observers,
      lensTransform Sys (encode p₁ q₁ hp₁ hq₁) o =
      lensTransform Sys (encode p₂ q₂ hp₂ hq₂) o) →
    ({p₁, q₁} : Multiset ℕ) = {p₂, q₂}



-- ═══════════════════════════════════════════════════════════════════════════════
-- §11. CONCRETE DIRECT-OBSERVATION SYSTEM
-- ═══════════════════════════════════════════════════════════════════════════════

/-- A direct-observation system on `Fin n`: edge cost 0 on diagonal, M off. -/
def directObsSys (n : ℕ) (hn : 0 < n) (M : ℕ) : BerggrenLensSystem where
  Node := Fin n
  instNonempty := ⟨⟨0, hn⟩⟩
  source := fun _ => 0
  observers := Finset.univ
  obs_nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  edgeCost := fun s o => if s = o then 0 else M

/-
In a direct-obs system, the lens transform at observer o is ≤ S o.
-/

/-
In a direct-obs system with M > max S, the transform equals S o.
-/

/-
Direct-obs systems separate bounded sources: equal delay profiles ⟹ equal.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- §12. DELAY RANK DATA
-- ═══════════════════════════════════════════════════════════════════════════════

def delayRankData (Sys : BerggrenLensSystem) (i j : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Sys.Node =>
    Sys.source s ≤ i ∧
    Finset.univ.inf' Finset.univ_nonempty (fun o => Sys.edgeCost s o) ≤ j)).card



-- ═══════════════════════════════════════════════════════════════════════════════
-- §13. PYTHAGOREAN SHELL CONNECTION
-- ═══════════════════════════════════════════════════════════════════════════════

structure PrimPythTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  pyth : a ^ 2 + b ^ 2 = c ^ 2
  a_pos : 0 < a
  b_pos : 0 < b

inductive BerggrenGenerator | A | B | C
  deriving DecidableEq, Fintype

structure PythagoreanShell (Sys : BerggrenLensSystem) where
  assignment : Sys.Node → PrimPythTriple
  source_from_a : Sys.source = fun n => (assignment n).a
  cost_from_hyp : ∀ s o, Sys.edgeCost s o =
    Int.natAbs ((assignment s).c - (assignment o).c : ℤ)


-- ═══════════════════════════════════════════════════════════════════════════════
-- §14. MYHILL-NERODE ANALOGY
-- ═══════════════════════════════════════════════════════════════════════════════

def delayNodeEquiv (Sys : BerggrenLensSystem) (s₁ s₂ : Sys.Node) : Prop :=
  ∀ o : Sys.Node, Sys.edgeCost s₁ o = Sys.edgeCost s₂ o

instance delayNodeEquiv_decidable (Sys : BerggrenLensSystem) :
    DecidableRel (delayNodeEquiv Sys) := fun _ _ => Fintype.decidableForallFintype

theorem delayNodeEquiv_equiv (Sys : BerggrenLensSystem) :
    Equivalence (delayNodeEquiv Sys) :=
  ⟨fun _ _ => rfl, fun h o => (h o).symm, fun h₁ h₂ o => (h₁ o).trans (h₂ o)⟩

def myhillNerodeQuotient (Sys : BerggrenLensSystem) :=
  Quotient ⟨delayNodeEquiv Sys, delayNodeEquiv_equiv Sys⟩

instance (Sys : BerggrenLensSystem) : Fintype (myhillNerodeQuotient Sys) :=
  @Quotient.fintype _ Sys.instFintype ⟨delayNodeEquiv Sys, delayNodeEquiv_equiv Sys⟩
    (delayNodeEquiv_decidable Sys)


-- ═══════════════════════════════════════════════════════════════════════════════
-- §15. FACTORING PIPELINE
-- ═══════════════════════════════════════════════════════════════════════════════


/-
═══════════════════════════════════════════════════════════════════════════════
§16. COMPLETE DUALITY THEOREM
═══════════════════════════════════════════════════════════════════════════════

**Complete Berggren Tropical Lens Duality.**
    1. Reconstruction: same delay profile ⟹ observational equivalence
    2. Canonical realization exists
    3. The Myhill–Nerode quotient is bounded
-/

end BerggrenTropicalLens

end


