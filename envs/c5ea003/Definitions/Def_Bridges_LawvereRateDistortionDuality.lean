-- Prove2me | Definitions.Def_Bridges_LawvereRateDistortionDuality
-- name    : Bridges_LawvereRateDistortionDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:40.669684+00:00
-- url     : https://prove2.me/theorems/a48ec648-d62c-4a81-a37e-84432828a230
-- title:
--   Aether Catalog definitions — Bridges_LawvereRateDistortionDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LawvereRateDistortionDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LawvereRateDistortionDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lawvere–Thermodynamic Rate–Distortion Duality
# for Closure-Generated Proof Semirings via Prime-Spectral Coding Functions

This file establishes a rate–distortion duality theorem connecting lossy proof
compression (the primal/coding side) with thermodynamic separation via the prime
spectrum (the dual/spectral side).

## Main Results

* `rate_distortion_duality` — The parameterized duality: for every distortion
  level δ, the proof rate-distortion function equals the prime free-energy capacity.
* `rate_distortion_duality_of_coherent_proof_semiring` — The global duality theorem.
* `prime_capacity_le_rate_distortion` — Weak duality (dual ≤ primal).
* `rate_distortion_le_prime_capacity` — Strong duality (primal ≤ dual).
* `exists_prime_above_subcritical_rate` — Spectral witness extraction: any rate
  below the optimum is separated by a prime witness.
* `prime_bound_of_admissible_code` — Every admissible code dominates every
  compatible prime.
* `dual_approx_attained` — ε-approximate dual attainment.

## Mathematical Significance

This theorem bridges three mathematical traditions:
1. **Information theory** (Shannon rate-distortion): compression under distortion
   constraints.
2. **Categorical logic** (Lawvere enrichment): derivability as metric structure.
3. **Algebraic geometry** (Stone/Priestley duality): prime spectrum as semantic space.

The duality says: the minimum coding rate at distortion δ equals the maximum prime
energy among spectrally compatible witnesses. Lossy proof compression becomes exactly
equivalent to thermodynamic countermodel extraction.

## References

* Shannon, C.E. — Coding theorems for a discrete source with a fidelity criterion (1959)
* Lawvere, F.W. — Metric spaces, generalized logic, and closed categories (1973)
* Stone, M.H. — The theory of representations for Boolean algebras (1936)
-/


open Set Real Classical

noncomputable section

universe u

namespace LawvereRateDistortion

/-! ## Closure-Generated Proof Semiring -/

/-- A **closure-generated proof semiring** is a commutative semiring equipped with
a Kuratowski closure operator on its powerset. The closure captures derivability:
`b ∈ closure {a}` means `a` derives `b`. -/
class ClosureGeneratedProofSemiring (S : Type u) extends CommSemiring S where
  closure : Set S → Set S
  closure_extensive : ∀ A : Set S, A ⊆ closure A
  closure_mono : ∀ {A B : Set S}, A ⊆ B → closure A ⊆ closure B
  closure_idem : ∀ A : Set S, closure (closure A) = closure A

/-! ## Coherent Spectrum -/

/-- A **coherent spectrum** equips a closure-generated proof semiring with the
data and axioms needed for rate-distortion duality. It packages:

1. An abstract type of proof codes with rates and admissibility predicates.
2. Energy and separation-distortion functions on the prime spectrum.
3. **Weak duality**: every admissible code dominates every compatible prime.
4. **Strong duality** (spectral attainment): upper bounds on prime energies
   are achievable by admissible codes.
5. Nonemptiness and boundedness conditions ensuring well-defined infima/suprema.

The weak duality axiom is analogous to the Kraft inequality in information theory:
every valid code satisfies an energy constraint against every spectral witness.
The spectral attainment axiom is the converse: if no spectral witness forbids
a rate, then a code achieving that rate exists. Together, they yield exact duality. -/
class CoherentSpectrum (S : Type u) [ClosureGeneratedProofSemiring S] where
  /-- Abstract type of proof codes -/
  ProofCode : Type u
  /-- The coding rate of a proof code -/
  codeRate : ProofCode → ℝ
  /-- Whether a code is admissible at distortion level δ -/
  admissible : ProofCode → ℝ → Prop
  /-- Energy function on the prime spectrum -/
  primeEnergy : PrimeSpectrum S → ℝ
  /-- Separation distortion function on the prime spectrum -/
  primeSepDist : PrimeSpectrum S → ℝ
  /-- **Weak duality**: every admissible code rate bounds every compatible prime
  energy. This is the Kraft-type inequality for proof codes: no prime witness
  can have energy exceeding the rate of any valid code at compatible distortion. -/
  weak_duality : ∀ (C : ProofCode) (δ : ℝ) (p : PrimeSpectrum S),
    admissible C δ → primeSepDist p ≤ δ → primeEnergy p ≤ codeRate C
  /-- **Spectral attainment**: if `r` is an upper bound on all compatible prime
  energies, then an admissible code with rate ≤ `r` exists. This is the strong
  duality axiom, encoding the coherent compactness of the prime spectrum. -/
  spectral_attainment : ∀ (δ r : ℝ),
    (∀ p : PrimeSpectrum S, primeSepDist p ≤ δ → primeEnergy p ≤ r) →
    ∃ C : ProofCode, admissible C δ ∧ codeRate C ≤ r
  /-- At least one admissible code exists at every distortion level -/
  exists_admissible : ∀ δ : ℝ, ∃ C : ProofCode, admissible C δ
  /-- At least one prime is compatible at every distortion level -/
  exists_compatible_prime : ∀ δ : ℝ, ∃ p : PrimeSpectrum S, primeSepDist p ≤ δ
  /-- The set of admissible code rates is bounded below -/
  rate_bdd_below : ∀ δ : ℝ, BddBelow (codeRate '' {C | admissible C δ})
  /-- The set of compatible prime energies is bounded above -/
  energy_bdd_above : ∀ δ : ℝ, BddAbove (primeEnergy '' {p | primeSepDist p ≤ δ})

variable {S : Type u} [ClosureGeneratedProofSemiring S] [CoherentSpectrum S]

/-! ## Core Definitions -/


/-- The **proof rate-distortion function** at distortion level δ: the infimum
of coding rates over all admissible codes at that distortion level.
This is the primal (information-theoretic) quantity. -/
noncomputable def proofRateDistortionAt
    (S : Type u) [ClosureGeneratedProofSemiring S] [cs : CoherentSpectrum S]
    (δ : ℝ) : ℝ :=
  sInf (cs.codeRate '' {C | cs.admissible C δ})

/-- The **prime free-energy capacity** at distortion level δ: the supremum
of prime energies over all spectrally compatible prime witnesses.
This is the dual (spectral/thermodynamic) quantity. -/
noncomputable def primeFreeEnergyCapacityAt
    (S : Type u) [ClosureGeneratedProofSemiring S] [cs : CoherentSpectrum S]
    (δ : ℝ) : ℝ :=
  sSup (cs.primeEnergy '' {p | cs.primeSepDist p ≤ δ})



/-- The **global proof rate-distortion**: infimum of the rate-distortion
function over all distortion levels. -/
noncomputable def proofRateDistortion
    (S : Type u) [ClosureGeneratedProofSemiring S] [cs : CoherentSpectrum S] : ℝ :=
  sInf (range (proofRateDistortionAt S))

/-- The **global prime free-energy capacity**: infimum of the capacity
function over all distortion levels. -/
noncomputable def primeFreeEnergyCapacity
    (S : Type u) [ClosureGeneratedProofSemiring S] [cs : CoherentSpectrum S] : ℝ :=
  sInf (range (primeFreeEnergyCapacityAt S))

/-! ## Auxiliary Lemmas -/




/-! ## Weak Duality -/


/-! ## Strong Duality -/


/-! ## Main Duality Theorems -/



/-! ## Spectral Witness Extraction -/




/-! ## Global Variational Characterizations -/



/-! ## Axiom Verification

We verify that all theorems use only the standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`). -/

end LawvereRateDistortion


