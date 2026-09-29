-- Prove2me | Definitions.Def_Bridges_TropicalOneWayKernelDuality
-- name    : Bridges_TropicalOneWayKernelDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:47.677186+00:00
-- url     : https://prove2.me/theorems/399774a4-11a1-425f-bc19-0bc6fe19a04a
-- title:
--   Aether Catalog definitions — Bridges_TropicalOneWayKernelDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalOneWayKernelDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalOneWayKernelDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical One-Way Kernel Duality via Idempotent Kernel Semimodules

## Bridge: Tropical Algebra ↔ Speculative Cryptography ↔ Realization Theory

This file formalizes a representation-theoretic approach to tropical one-way structure.
One-way behavior in tropical hash networks is encoded intrinsically by an
**idempotent kernel semimodule** rather than operationally by circuits.

## Main Results

* `kernelProfile_symm` — kernel profiles are symmetric
* `kernelProfile_le_witness` / `kernelProfile_exists_witness` — witness bounds
* `tropicalGram_symm` — tropical Gram symmetry
* `self_composition_eq_of_zero_diag` — idempotent kernel characterization
* `idempotent_iff_metric` — tropical metrics = idempotent kernels
* `composeKernelProfiles_symm` — functoriality under composition
* `reconstructNetwork_kernelProfile_eq` — certified reconstruction
* `reconstructNetwork_matches_kernel` — recovery bound
* `distKernel_idempotent` — concrete idempotent example

## Cross-Domain Connections

- **Automata / Myhill–Nerode**: Kernel profiles as indistinguishability invariants
- **Control theory**: Generator rank mirrors Hankel-rank minimality
- **Cryptography**: Collision-separation via algebraic certificates
- **Tropical geometry**: Kernel profile = tropical Gram matrix
- **Complexity theory**: Realization size as structural complexity
-/

noncomputable section

open Finset BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace TropicalOneWayKernelDuality

/-! ## Section 1: Min-Plus Matrix Arithmetic -/

variable {n : ℕ}

/-- Min-plus matrix multiplication: (A ⊗ B)ᵢⱼ = min_k (Aᵢₖ + Bₖⱼ). -/
def tropMul' (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Finset.univ.inf' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun k => A i k + B k j)




/-! ## Section 2: Bounded Tropical Hash Networks -/

/-- A bounded tropical hash network on `Fin n`. -/
structure BoundedTropicalHashNetwork (n : ℕ) (hn : 0 < n) where
  layerCount : ℕ
  layers : Fin layerCount → Matrix (Fin n) (Fin n) ℝ
  bound : ℝ
  entries_bounded : ∀ l i j, |layers l i j| ≤ bound

/-- Network evaluation: first layer (zero matrix for empty network). -/
def BoundedTropicalHashNetwork.eval {hn : 0 < n}
    (H : BoundedTropicalHashNetwork n hn) : Matrix (Fin n) (Fin n) ℝ :=
  if h : H.layerCount = 0 then fun _ _ => 0
  else H.layers ⟨0, Nat.pos_of_ne_zero h⟩

/-- Kernel profile: κ(a,b) = min_k (M(a,k) + M(b,k)). -/
def BoundedTropicalHashNetwork.kernelProfile {hn : 0 < n}
    (H : BoundedTropicalHashNetwork n hn) : Fin n → Fin n → ℝ :=
  fun a b => Finset.univ.inf' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun k => H.eval a k + H.eval b k)

/-! ## Section 3: Kernel Profile Properties -/




/-! ## Section 4: Tropical Gram Matrix -/

/-- Tropical Gram matrix: G_{ab} = min_k (M_{ak} + M_{bk}). -/
def tropicalGram (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → Fin n → ℝ :=
  fun a b => Finset.univ.inf' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun k => M a k + M b k)





/-! ## Section 5: Composition of Kernel Profiles -/

/-- Tropical composition: (κ₁ ⊗ κ₂)(a,c) = min_b (κ₁(a,b) + κ₂(b,c)). -/
def composeKernelProfiles (hn : 0 < n)
    (κ₁ κ₂ : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun a c => Finset.univ.inf' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun b => κ₁ a b + κ₂ b c)




/-! ## Section 6: Network Composition -/

/-- Compose two networks by concatenating layers. -/
def BoundedTropicalHashNetwork.comp {hn : 0 < n}
    (H₂ H₁ : BoundedTropicalHashNetwork n hn) :
    BoundedTropicalHashNetwork n hn where
  layerCount := H₁.layerCount + H₂.layerCount
  layers := fun l =>
    if h : l.val < H₁.layerCount then H₁.layers ⟨l.val, h⟩
    else H₂.layers ⟨l.val - H₁.layerCount, by omega⟩
  bound := max H₁.bound H₂.bound
  entries_bounded := by
    intro l i j; split
    · exact le_trans (H₁.entries_bounded _ i j) (le_max_left _ _)
    · exact le_trans (H₂.entries_bounded _ i j) (le_max_right _ _)


/-! ## Section 7: Tropical Kernel Distance -/

/-- Normalized tropical kernel distance: d(a,b) = κ(a,b) - (κ(a,a) + κ(b,b))/2. -/
def tropKernelDist (κ : Fin n → Fin n → ℝ) (a b : Fin n) : ℝ :=
  κ a b - (κ a a + κ b b) / 2



/-! ## Section 8: Idempotent Kernel Theory

**Central theorem**: κ ⊗ κ = κ ↔ κ is a tropical (pseudo)metric. -/




/-! ## Section 9: Finite Tropical Kernel Semimodule -/

/-- A finite tropical kernel semimodule with generators. -/
structure FiniteTropKernelSemimodule (n : ℕ) (hn : 0 < n) where
  κ : Fin n → Fin n → ℝ
  generators : Finset (Fin n)
  generators_nonempty : generators.Nonempty
  span_eq : ∀ a b, κ a b = generators.inf' generators_nonempty
    (fun g => κ a g + κ g b)

def generatorRank {hn : 0 < n} (K : FiniteTropKernelSemimodule n hn) : ℕ :=
  K.generators.card



/-! ## Section 10: Network Reconstruction -/

/-- Build a 1-layer network from a kernel semimodule. -/
def reconstructNetwork (hn : 0 < n) (K : FiniteTropKernelSemimodule n hn) :
    BoundedTropicalHashNetwork n hn where
  layerCount := 1
  layers := fun _ a b => K.κ a b
  bound := Finset.univ.sup' (univ_nonempty_iff.mpr ⟨(⟨0, hn⟩ : Fin n)⟩)
    (fun i => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨(⟨0, hn⟩ : Fin n)⟩)
      (fun j => |K.κ i j|))
  entries_bounded := by
    intro _ i j
    exact le_trans
      (Finset.le_sup' (fun j' => |K.κ i j'|) (Finset.mem_univ j))
      (Finset.le_sup'
        (fun i' => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨(⟨0, hn⟩ : Fin n)⟩)
          (fun j' => |K.κ i' j'|))
        (Finset.mem_univ i))





/-! ## Section 11: Concrete Examples -/

/-- Distance kernel on Fin 2: 0 on diagonal, d off-diagonal. -/
def distKernel (d : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a b => if a = b then 0 else d





/-! ## Section 12: Recovery for Tropical Metrics -/


/-! ## Section 13: Distinct Witness Count -/

/-- Number of optimal witnesses for some pair. -/
def distinctWitnessCount (hn : 0 < n) (κ : Fin n → Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    ∃ a b : Fin n, κ a b = κ a k + κ k b)).card


/-! ## Section 14: Duality Summary

| Direction | Theorem | Description |
|-----------|---------|-------------|
| Forward | `kernelProfile_eq_tropicalGram` | Network → Gram kernel |
| Symmetry | `kernelProfile_symm` | Kernel profiles symmetric |
| Witness | `kernelProfile_exists_witness` | Witnesses exist |
| Idempotent | `idempotent_iff_metric` | Metric ↔ Idempotent |
| Composition | `composeKernelProfiles_symm` | Functorial |
| Reconstruction | `reconstructNetwork_matches_kernel` | Certified bound |
| Recovery | `reconstructed_kernel_recovers_metric` | Metric recovery |
-/

end TropicalOneWayKernelDuality


