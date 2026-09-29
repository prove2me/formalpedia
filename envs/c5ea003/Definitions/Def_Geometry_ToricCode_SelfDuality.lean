-- Prove2me | Definitions.Def_Geometry_ToricCode_SelfDuality
-- name    : Geometry_ToricCode_SelfDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:58:49.459381+00:00
-- url     : https://prove2.me/theorems/1420f757-2e1d-43cd-aa95-a1ee262ccd24
-- title:
--   Aether Catalog definitions — Geometry_ToricCode_SelfDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ToricCode.SelfDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ToricCode/SelfDuality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Dual
/-!
# Abstract self-duality: when are the `X`- and `Z`-spectra equal?

`ToricCode.dualLogicalWeights_eq` proved that the primal and dual logical weight
spectra of the square-grid torus coincide, by exhibiting one explicit
quarter-turn permutation of the qubit set.  This file isolates *exactly* what
that argument used, answering sub-conjecture 3 of the previous cycle's
`FUTURE_DIRECTIONS.md`.

We introduce

* `BinaryCSS V E F` — a three-term binary chain complex `𝔽₂^F → 𝔽₂^E → 𝔽₂^V`
  given by two matrices with `A * B = 0`, i.e. a CSS code with qubit set `E`,
  `Z`-checks `V` and `X`-checks `F`;
* `BinaryCSS.SelfDual` — the *data* of a weight-preserving self-duality: a
  permutation `τ` of the qubits together with bijections `σ : F ≃ V` and
  `ρ : V ≃ F` of the two check sets, satisfying the two intertwining identities
  `Bᵀ(z ∘ τ) = (A z) ∘ σ` and `(B g) ∘ τ = Aᵀ (g ∘ ρ)`.

The main theorem `BinaryCSS.SelfDual.logicalWeights_eq` says that such data
forces the *full* primal and dual logical weight spectra to be equal as subsets
of `ℕ` — hence in particular `d_X = d_Z` (`SelfDual.dualDistance_eq`).  No
finiteness of the field, no surface, no locality is used: the statement is pure
linear algebra over `𝔽₂` plus a bijection.

Finally `toricSelfDual` exhibits the `M × N` torus as an instance, so the
concrete result of `ToricCode.Dual` is recovered from the general principle.
-/

open Matrix

namespace ToricCode

/-- A binary CSS code: a three-term chain complex `𝔽₂^F --B--> 𝔽₂^E --A--> 𝔽₂^V`
over `𝔽₂`.  `E` is the qubit set, `V` indexes the `Z`-checks and `F` the
`X`-checks. -/
structure BinaryCSS (V E F : Type*) [Fintype V] [Fintype E] [Fintype F] [DecidableEq E] where
  /-- The boundary map `∂₁` (the `Z`-check matrix). -/
  A : Matrix V E F2
  /-- The boundary map `∂₂` (the `X`-check matrix). -/
  B : Matrix E F F2
  /-- The chain condition `∂₁ ∘ ∂₂ = 0`. -/
  chain : A * B = 0

namespace BinaryCSS

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F] [DecidableEq E]
variable (C : BinaryCSS V E F)

/-- `Z`-cycles: chains with trivial syndrome. -/
noncomputable def cycles : Submodule F2 (E → F2) := LinearMap.ker C.A.mulVecLin

/-- `Z`-boundaries: the stabiliser group. -/
noncomputable def boundaries : Submodule F2 (E → F2) := LinearMap.range C.B.mulVecLin

/-- `X`-cycles of the dual (cochain) complex. -/
noncomputable def dualCycles : Submodule F2 (E → F2) := LinearMap.ker (C.Bᵀ).mulVecLin

/-- `X`-boundaries of the dual (cochain) complex. -/
noncomputable def dualBoundaries : Submodule F2 (E → F2) := LinearMap.range (C.Aᵀ).mulVecLin


/-- Weights of the undetectable non-stabiliser (`Z`-type) errors. -/
def logicalWeights : Set ℕ :=
  {w | ∃ z : E → F2, z ∈ C.cycles ∧ z ∉ C.boundaries ∧ hammingNorm z = w}

/-- Weights of the undetectable non-stabiliser (`X`-type) errors. -/
def dualLogicalWeights : Set ℕ :=
  {w | ∃ z : E → F2, z ∈ C.dualCycles ∧ z ∉ C.dualBoundaries ∧ hammingNorm z = w}

/-- The `Z`-distance. -/
noncomputable def distance : ℕ := sInf C.logicalWeights

/-- The `X`-distance. -/
noncomputable def dualDistance : ℕ := sInf C.dualLogicalWeights

/-- **Self-duality data** for a binary CSS code: a permutation `τ` of the qubits
together with bijections `σ, ρ` between the two check sets, intertwining the
boundary map with the dual boundary map and boundaries with coboundaries. -/
structure SelfDual (C : BinaryCSS V E F) where
  /-- The weight-preserving relabelling of the qubits. -/
  tau : E ≃ E
  /-- The matching of `X`-checks with `Z`-checks used by the cycle identity. -/
  sigma : F ≃ V
  /-- The matching of `Z`-checks with `X`-checks used by the boundary identity. -/
  rho : V ≃ F
  /-- `τ` turns the boundary map into the dual boundary map. -/
  intertwine_cycle : ∀ z : E → F2, (C.Bᵀ) *ᵥ (z ∘ tau) = (C.A *ᵥ z) ∘ sigma
  /-- `τ` turns boundaries into coboundaries. -/
  intertwine_boundary : ∀ g : F → F2, (C.B *ᵥ g) ∘ tau = (C.Aᵀ) *ᵥ (g ∘ rho)

namespace SelfDual

variable {C}




end SelfDual

end BinaryCSS

/-! ### The torus is an instance -/

variable (M N : ℕ) [NeZero M] [NeZero N]

/-- The `M × N` torus as an abstract binary CSS code. -/
def toricCSS : BinaryCSS (Vert M N) (Edge M N) (Face M N) where
  A := d1 M N
  B := d2 M N
  chain := by
    ext v f
    have h2 : ((d1 M N * d2 M N) *ᵥ (Pi.single f (1 : F2))) v = 0 := by
      rw [← Matrix.mulVec_mulVec, d1_d2_mulVec]; rfl
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2

/-- **The quarter turn makes the torus code self-dual**, in the abstract sense
of `BinaryCSS.SelfDual`. -/
def toricSelfDual : (toricCSS M N).SelfDual where
  tau := tauEquiv M N
  sigma := Equiv.refl _
  rho := Equiv.subRight (1, 1)
  intertwine_cycle z := by simpa using d2T_mulVec_comp_tau M N z
  intertwine_boundary g := d2_comp_tau M N g




end ToricCode


