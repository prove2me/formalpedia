-- Prove2me | Definitions.Def_Bridges_IdempotentGaugeCurvatureDuality
-- name    : Bridges_IdempotentGaugeCurvatureDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:27.733366+00:00
-- url     : https://prove2.me/theorems/149f1c26-1342-44e8-8b77-247b8c0be4cd
-- title:
--   Aether Catalog definitions — Bridges_IdempotentGaugeCurvatureDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IdempotentGaugeCurvatureDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IdempotentGaugeCurvatureDuality.lean by skeleton subtraction
import Mathlib
/-
# Idempotent Gauge–Curvature Duality via Closure Connection Theory

This file establishes a formal foundation for **idempotent gauge theory on finite
closure systems**. The key insight is that closure-based emergent geometries support
a genuine gauge theory with flatness/reconstruction duality: local transport data,
holonomy obstruction, gauge equivalence, and cohomological classification.

## Main Results

### Core Algebraic Framework (any additive abelian group)
* `ofPotential_isCocycle` — A connection induced by a potential is automatically flat
* `cocycle_implies_potential` — A flat connection admits a global potential
* `flat_iff_potential` — **Flatness ↔ existence of a global potential** (main duality)

### Path Transport
* `transport_eq_weight` — Flat connections yield path-independent transport
* `transport_path_independent` — Two paths, same endpoints → same transport

### Gauge Theory
* `potential_unique_mod_gauge` — Potentials unique up to global gauge shift
* `gaugeEquiv_iff_same_connection` — Gauge-equivalent ↔ same connection

### Closure System
* `closureFlat_iff_potential` — Flat ↔ potential for closure connections

### Certified Reconstruction
* `certifiedReconstruct` — Returns either a potential or a curvature witness
* `curvatureWitness_sound` — Witnesses certify non-flatness

### First Closure Cohomology
* `coboundary_sq_zero` — δ₁ ∘ δ₀ = 0
* `H1_trivial_of_nonempty` — H¹ = 0 when vertex set is nonempty
-/


set_option maxHeartbeats 400000

namespace ClosureGauge

/-! ## Part 1: Core Connection Framework -/

/-- A connection on vertex set `V` with values in `G`.
Assigns a "transport weight" to each ordered pair of vertices. -/
@[ext]
structure Connection (V : Type*) (G : Type*) where
  weight : V → V → G

variable {V : Type*} {G : Type*} [AddCommGroup G]

/-- A connection is **flat** (cocycle) if weights compose additively. -/
def Connection.IsCocycle (A : Connection V G) : Prop :=
  ∀ u v w : V, A.weight u v + A.weight v w = A.weight u w

/-- A connection is **induced by a potential** `φ` if `w(u,v) = φ(v) - φ(u)`. -/
def Connection.InducedByPotential (A : Connection V G) (φ : V → G) : Prop :=
  ∀ u v : V, A.weight u v = φ v - φ u

/-- The connection induced by a potential function. -/
def Connection.ofPotential (φ : V → G) : Connection V G :=
  ⟨fun u v => φ v - φ u⟩


/-
Cocycle self-weight vanishes: `w(v,v) = 0`.
-/

/-
**Easy direction**: Potential-induced connections are flat.
-/

/-
**Hard direction**: Flat connections admit global potentials.
-/

/-
**Main Duality Theorem**: Flat ↔ existence of global potential.
-/

/-! ## Part 2: Path Transport -/

/-- Transport of a weight function along a list-based path `[v₀, v₁, ..., vₙ]`.
Returns the sum `w(v₀,v₁) + w(v₁,v₂) + ... + w(vₙ₋₁,vₙ)`. -/
def listTransport (f : V → V → G) : List V → G
  | [] => 0
  | [_] => 0
  | a :: b :: rest => f a b + listTransport f (b :: rest)


/-
For flat connections, transport along any path `[u, ..., v]` equals `f(u,v)`.
This is the key path-independence result.
-/

/-
**Path-Independence**: For flat connections, two paths with the same
endpoints yield the same transport.
-/

/-
**Transport Composition**: Transport along a concatenated path with
a shared vertex equals the sum of transports.
-/

/-! ## Part 3: Gauge Theory -/

/-- Two potentials are **gauge-equivalent** if they differ by a global constant. -/
def GaugeEquiv (φ ψ : V → G) : Prop :=
  ∃ c : G, ∀ v : V, ψ v = φ v + c




/-
**Gauge Uniqueness**: Two potentials inducing the same connection are
gauge-equivalent (differ by a constant).
-/

/-
Gauge-equivalent potentials induce the same connection.
-/

/-! ## Part 4: Closure System Instantiation -/

/-- A closure operator on `Finset α`. -/
structure ClosureOp (α : Type*) [Fintype α] [DecidableEq α] where
  cl : Finset α → Finset α
  extensive : ∀ s, s ⊆ cl s
  monotone : ∀ {s t}, s ⊆ t → cl s ⊆ cl t
  idempotent : ∀ s, cl (cl s) = cl s

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set is **closed** if it is a fixpoint of the closure operator. -/
def ClosureOp.IsClosed (C : ClosureOp α) (s : Finset α) : Prop := C.cl s = s

/-- The type of closed sets of a closure operator. -/
def ClosedSet (C : ClosureOp α) := { s : Finset α // C.IsClosed s }

instance closedSetDecEq (C : ClosureOp α) : DecidableEq (ClosedSet C) :=
  fun a b => decidable_of_iff (a.1 = b.1) ⟨Subtype.ext, congr_arg Subtype.val⟩

/-- The closure of any set is closed. -/
theorem ClosureOp.isClosed_cl (C : ClosureOp α) (s : Finset α) :
    C.IsClosed (C.cl s) := C.idempotent s

/-- Closed sets are nonempty: cl(∅) is always closed. -/
noncomputable instance closedSetNonempty (C : ClosureOp α) :
    Nonempty (ClosedSet C) :=
  ⟨⟨C.cl ∅, C.isClosed_cl ∅⟩⟩


/-! ## Part 5: Certified Reconstruction -/

/-- Reconstruct a potential from a flat connection by basepoint transport. -/
noncomputable def reconstructPotential [Nonempty V] (A : Connection V G) : V → G :=
  fun v => A.weight (Classical.arbitrary V) v

/-
The reconstructed potential correctly induces the original flat connection.
-/

/-- A curvature witness: a triple where the cocycle condition fails. -/
structure CurvatureWitness (V : Type*) (G : Type*) [AddCommGroup G]
    (A : Connection V G) where
  u : V
  v : V
  w : V
  witness : A.weight u v + A.weight v w ≠ A.weight u w



/-
A curvature witness certifies non-flatness.
-/


/-! ## Part 6: Cochain Complex and First Closure Cohomology -/

/-- Coboundary δ₀: 0-cochains → 1-cochains. Maps potential to connection. -/
def coboundary₀ (φ : V → G) : V → V → G :=
  fun u v => φ v - φ u

/-- Coboundary δ₁: 1-cochains → 2-cochains. Measures curvature. -/
def coboundary₁ (w : V → V → G) : V → V → V → G :=
  fun u v x => w u v + w v x - w u x

/-
**Fundamental Identity**: δ₁ ∘ δ₀ = 0. Every coboundary is a cocycle.
-/

/-- A 1-cochain is a **cocycle** if it is in ker δ₁. -/
def IsCocycle₁ (w : V → V → G) : Prop :=
  ∀ u v x, coboundary₁ w u v x = 0

/-- A 1-cochain is a **coboundary** if it is in im δ₀. -/
def IsCoboundary₁ (w : V → V → G) : Prop :=
  ∃ φ : V → G, w = coboundary₀ φ

/-
Every coboundary is a cocycle.
-/

/-
**H¹ Triviality**: Every cocycle is a coboundary when V is nonempty.
H¹(V, G) = 0 — the cohomological formulation of the main duality.
-/


end ClosureGauge


