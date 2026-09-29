-- Prove2me | Definitions.Def_Bridges_MolecularComputingLimitsV25_MolecularComputingLimits
-- name    : Bridges_MolecularComputingLimitsV25_MolecularComputingLimits
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:26.626986+00:00
-- url     : https://prove2.me/theorems/fab56e11-ccc2-4ca3-a433-90e59faa8937
-- title:
--   Aether Catalog definitions — Bridges_MolecularComputingLimitsV25_MolecularComputingLimits
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.MolecularComputingLimitsV25.MolecularComputingLimits`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/MolecularComputingLimitsV25/MolecularComputingLimits.lean by skeleton subtraction
import Mathlib

/-!
# Molecular computing limits: exact finite-state CRN simulation and preparation cost

This file isolates two rigorous cores of the broad molecular-computing programme.

First, a chemical reaction network is given discrete mass-action semantics: a reaction
is enabled when every reactant count is available, and firing subtracts reactants and
adds products.  Every deterministic transition system on a finite configuration type
is compiled into unary reactions.  Starting from a one-hot molecular population, one
reaction exactly simulates one machine step; induction gives exact finite-trace
simulation and conservation of one-hot mass.

Second, an explicit cost model charges for preparing every molecular candidate.  If
one reaction round tests all prepared candidates in parallel, its elapsed time is
`p*n + 1`, versus `(p+1)*n` for sequential testing.  For positive preparation cost,
the sequential time is at most twice the molecular time.  Thus this model rules out
an exponential end-to-end speedup even though the reaction stage itself is fully
parallel.  This is a theorem about the stated cost model, not an empirical claim
about all laboratory implementations.

Finally, a bit-capacity model gives a description-length lower bound on volume.  It
makes precise the direction in which Kolmogorov complexity can constrain physical
volume, conditional on an encoding and a per-volume bit capacity.
-/

namespace MolecularComputingLimits

open Function

section CRNSimulation

variable {ι : Type*} [DecidableEq ι]

/-- A molecular population records the count of each species. -/
abbrev Population (ι : Type*) := ι → ℕ

/-- A discrete chemical reaction, represented by reactant and product stoichiometry. -/
structure Reaction (ι : Type*) where
  reactant : Population ι
  product : Population ι

/-- A reaction is enabled when all required reactants are present. -/
def Reaction.Enabled (r : Reaction ι) (x : Population ι) : Prop :=
  ∀ i, r.reactant i ≤ x i

/-- Discrete firing semantics: consume reactants and then produce products. -/
def Reaction.fire (r : Reaction ι) (x : Population ι) : Population ι :=
  fun i => x i - r.reactant i + r.product i

/-- The one-hot population encoding a single machine configuration. -/
def oneHot (q : ι) : Population ι := fun i => if i = q then 1 else 0

/-- Compile one deterministic transition `q ↦ next q` into a unary reaction. -/
def transitionReaction (next : ι → ι) (q : ι) : Reaction ι where
  reactant := oneHot q
  product := oneHot (next q)



/-- One CRN step, selecting the reaction indexed by the represented configuration. -/
def compiledStep (next : ι → ι) (q : ι) (x : Population ι) : Population ι :=
  (transitionReaction next q).fire x


/-- A recursively scheduled CRN execution that chooses the reaction for the current
machine configuration. -/
def runCompiled (next : ι → ι) : ℕ → ι → Population ι
  | 0, q => oneHot q
  | t + 1, q => compiledStep next ((next^[t]) q) (runCompiled next t q)



end CRNSimulation

section PreparationCost

/-- End-to-end elapsed time for a fully parallel molecular search over `n` candidates:
preparation is charged `p` steps per candidate and all tests then take one round. -/
def molecularTime (p n : ℕ) : ℕ := p * n + 1

/-- Time for preparing and testing `n` candidates sequentially. -/
def sequentialTime (p n : ℕ) : ℕ := (p + 1) * n







end PreparationCost

section DescriptionVolume

/-- A physical encoding with volume `v` and capacity `b` bits per volume unit can
carry a description of length `k` only if `k ≤ b*v`. -/
def FitsDescription (bitsPerVolume volume complexity : ℕ) : Prop :=
  complexity ≤ bitsPerVolume * volume



/-- The information-theoretic minimum volume at capacity `b` is ceiling division. -/
def minimumVolume (bitsPerVolume complexity : ℕ) : ℕ :=
  complexity ⌈/⌉ bitsPerVolume



end DescriptionVolume

end MolecularComputingLimits


