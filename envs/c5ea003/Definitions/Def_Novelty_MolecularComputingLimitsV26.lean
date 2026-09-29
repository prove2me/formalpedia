-- Prove2me | Definitions.Def_Novelty_MolecularComputingLimitsV26
-- name    : Novelty_MolecularComputingLimitsV26
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:46.352063+00:00
-- url     : https://prove2.me/theorems/9a27f150-c125-44e5-812e-715edab0b08d
-- title:
--   Aether Catalog definitions — Novelty_MolecularComputingLimitsV26
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.MolecularComputingLimitsV26`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/MolecularComputingLimitsV26.lean by skeleton subtraction
import Mathlib

/-!
# Molecular computing limits: a contrarian finite-state formalization

This file separates theorem-level consequences of explicit models from empirical
claims.  A discrete mass-action CRN exactly simulates every finite deterministic
transition system using one species per configuration and one unary reaction per
transition.  This supplies the finite-trace compiler underlying CRN universality,
but does not identify finite-state simulation with a finite universal Turing machine.

The resource results prove an exact ceiling-division volume law and a constant-factor
end-to-end parallel-search bound when candidate preparation is charged.  Two overly
bold variants are disproved: exact integral proportionality fails because of rounding,
and the constant-factor bound fails when preparation is free.  Finally, storage
capacity alone is shown not to imply any throughput ceiling or throughput guarantee.
-/

namespace MolecularComputingV26

open Function
open scoped BigOperators

section CRN

variable {ι : Type*} [DecidableEq ι]

/-- A population is a molecule count for every species. -/
abbrev Population (ι : Type*) := ι → ℕ

/-- Reactant and product stoichiometry of a discrete reaction. -/
structure Reaction (ι : Type*) where
  reactant : Population ι
  product : Population ι


/-- Fire a reaction by consuming reactants and producing products. -/
def Reaction.fire (r : Reaction ι) (x : Population ι) : Population ι :=
  fun i => x i - r.reactant i + r.product i

/-- One molecule of species `q` and no other molecules. -/
def oneHot (q : ι) : Population ι := fun i => if i = q then 1 else 0

/-- Compile transition `q ↦ next q` to the unary reaction `q → next q`. -/
def transitionReaction (next : ι → ι) (q : ι) : Reaction ι where
  reactant := oneHot q
  product := oneHot (next q)


/-- Scheduled execution of the compiled reactions. -/
def runCompiled (next : ι → ι) : ℕ → ι → Population ι
  | 0, q => oneHot q
  | t + 1, q => (transitionReaction next ((next^[t]) q)).fire (runCompiled next t q)


/-- Discrete stochastic mass-action propensity, using falling factorials. -/
def massActionPropensity [Fintype ι]
    (rate : ℕ) (r : Reaction ι) (x : Population ι) : ℕ :=
  rate * ∏ i, (x i).descFactorial (r.reactant i)



end CRN

section Volume

/-- A `k`-bit description fits volume `v` at density `b` when `k ≤ b*v`. -/
def FitsDescription (bitsPerVolume volume complexity : ℕ) : Prop :=
  complexity ≤ bitsPerVolume * volume

/-- Information-theoretic minimum volume at fixed bit density. -/
def minimumVolume (bitsPerVolume complexity : ℕ) : ℕ :=
  complexity ⌈/⌉ bitsPerVolume







end Volume

section Parallelism

/-- End-to-end molecular-search time: prepare `n` candidates at cost `p` each,
then test all candidates in one parallel round. -/
def molecularTime (p n : ℕ) : ℕ := p * n + 1

/-- Prepare and test the same candidates sequentially. -/
def sequentialTime (p n : ℕ) : ℕ := (p + 1) * n





end Parallelism

section ThroughputIndependence

/-- A deliberately minimal physical specification separating storage and throughput. -/
structure DeviceSpec where
  storageBits : ℕ
  operationsPerSecond : ℕ



end ThroughputIndependence

end MolecularComputingV26


