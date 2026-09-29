-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
-- name    : Bridges_InfiniteCubicMatchingsCompactness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:20.096933+00:00
-- url     : https://prove2.me/theorems/ec7d0350-fd8f-4243-8081-dd05dbb06524
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsCompactness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsCompactness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsCompactness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
/-
# Compactness: transferring the Berge–Fulkerson property from finite to infinite graphs

The paper *On some perfect matching conjectures in infinite, cubic, bridgeless graphs*
proves that the finite versions of the Berge–Fulkerson, Fan–Raspaud and Máčajová–Škoviera
conjectures are equivalent to their infinite versions.  The engine behind such statements is
a compactness (Rado selection / Tychonoff) argument.  This file formalises that engine.

Main results:

* `exists_forall_of_forall_finset` : a general compactness principle.  A constraint system on
  a product of *finite* sets, each constraint depending only on finitely many coordinates, is
  satisfiable as soon as every finite subsystem is.
* `bergeFulkerson_iff_locallyApproximable` : for a locally finite graph, the Berge–Fulkerson
  property is **finitary**: it holds iff every finite set of vertices carries a partial
  Berge–Fulkerson configuration.  (This is the exact local-to-global content of the transfer
  theorem.)
* `bergeFulkerson_of_finite_local_models` : if the *finite* Berge–Fulkerson conjecture holds
  and the (possibly infinite) locally finite graph `G` admits, around every finite set of
  vertices, a finite cubic bridgeless *local model*, then `G` satisfies Berge–Fulkerson.
-/

namespace Bridges.InfiniteCubicMatchings

universe u v w

/-! ## A general compactness principle -/


/-! ## Berge–Fulkerson configurations -/

variable {V : Type u} {G : SimpleGraph V}

/-- A *Berge–Fulkerson configuration* assigns to every vertex a `6`-tuple of neighbours
(the candidate partners in the six matchings). -/
abbrev BFConfig (G : SimpleGraph V) := ∀ v : V, Fin 6 → G.neighborSet v

/-- The local Berge–Fulkerson condition at a vertex `v`: the six partner maps are
involutive at `v`, and every edge at `v` is used by exactly two of them. -/
def BFCond (G : SimpleGraph V) (c : BFConfig G) (v : V) : Prop :=
  (∀ i : Fin 6, ((c ((c v i : V)) i : V) = v)) ∧
  (∀ w ∈ G.neighborSet v, {i : Fin 6 | (c v i : V) = w}.ncard = 2)

/-- `G` is *Berge–Fulkerson locally approximable* if every finite set of vertices carries a
partial Berge–Fulkerson configuration. -/
def BFLocallyApproximable (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, ∃ c : BFConfig G, ∀ v ∈ T, BFCond G c v




/-! ## Finite local models: the finite conjecture transfers to infinite graphs -/

variable {W : Type v}

/-- `φ : V → W` is a *local isomorphism at `v`* from `G` to `K` if it maps the neighbours of
`v` injectively onto the neighbours of `φ v`. -/
structure IsLocalIsoAt (G : SimpleGraph V) (K : SimpleGraph W) (φ : V → W) (v : V) : Prop where
  /-- neighbours are sent to neighbours -/
  adj : ∀ x, G.Adj v x → K.Adj (φ v) (φ x)
  /-- distinct neighbours have distinct images -/
  inj : ∀ x y, G.Adj v x → G.Adj v y → φ x = φ y → x = y
  /-- every neighbour of `φ v` is hit -/
  surj : ∀ y, K.Adj (φ v) y → ∃ x, G.Adj v x ∧ φ x = y


/-- The Berge–Fulkerson conjecture for *finite* cubic bridgeless graphs. -/
def FiniteBergeFulkersonConjecture : Prop :=
  ∀ (W : Type) (_ : Fintype W) (K : SimpleGraph W), IsCubic K → Bridgeless K → BergeFulkerson K


/-! ## The same for Fan–Raspaud and Máčajová–Škoviera

All three properties are *finitary*: they are determined by their restrictions to finite sets
of vertices.  We set up the two remaining cases with the same machinery. -/

/-- A `k`-tuple of candidate partners at each vertex. -/
abbrev MConfig (G : SimpleGraph V) (k : ℕ) := ∀ v : V, Fin k → G.neighborSet v

/-- The condition that the `k` partner maps are involutive at `v`. -/
def InvolCond (G : SimpleGraph V) {k : ℕ} (c : MConfig G k) (v : V) : Prop :=
  ∀ i : Fin k, ((c ((c v i : V)) i : V) = v)

/-- The `k` perfect matchings determined by a globally involutive configuration. -/
def toMatchings {k : ℕ} (c : MConfig G k) (h : ∀ v, InvolCond G c v) (i : Fin k) :
    PerfectMatching G :=
  ⟨fun v => (c v i : V), fun v => (c v i).2, fun v => h v i⟩



/-! ### Fan–Raspaud -/

/-- The local Fan–Raspaud condition at `v`: the three partner maps are involutive at `v`, and
no edge at `v` is used by all three. -/
def FRCond (G : SimpleGraph V) (c : MConfig G 3) (v : V) : Prop :=
  InvolCond G c v ∧ ∀ w ∈ G.neighborSet v, ¬ ∀ i : Fin 3, (c v i : V) = w

/-- `G` is *Fan–Raspaud locally approximable* if every finite set of vertices carries a
partial Fan–Raspaud configuration. -/
def FRLocallyApproximable (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, ∃ c : MConfig G 3, ∀ v ∈ T, FRCond G c v


/-! ### Máčajová–Škoviera -/

/-- The local Máčajová–Škoviera conditions, indexed by vertices (involutivity) and by finite
vertex sets (the odd cut condition). -/
def MSCond (G : SimpleGraph V) (c : MConfig G 2) : V ⊕ Finset V → Prop
  | Sum.inl v => InvolCond G c v
  | Sum.inr S => Odd S.card →
      ∃ u ∈ S, ∃ w, G.Adj u w ∧ w ∉ S ∧ ¬ ((c u 0 : V) = w ∧ (c u 1 : V) = w)

/-- `G` is *Máčajová–Škoviera locally approximable* if every finite family of local
conditions can be satisfied simultaneously. -/
def MSLocallyApproximable (G : SimpleGraph V) : Prop :=
  ∀ T : Finset (V ⊕ Finset V), ∃ c : MConfig G 2, ∀ j ∈ T, MSCond G c j


/-! ### Finite local models for Fan–Raspaud

The same pullback argument as for Berge–Fulkerson, one dimension lower. -/


/-- The Fan–Raspaud conjecture for *finite* cubic bridgeless graphs. -/
def FiniteFanRaspaudConjecture : Prop :=
  ∀ (W : Type) (_ : Fintype W) (K : SimpleGraph W), IsCubic K → Bridgeless K → FanRaspaud K


end Bridges.InfiniteCubicMatchings


