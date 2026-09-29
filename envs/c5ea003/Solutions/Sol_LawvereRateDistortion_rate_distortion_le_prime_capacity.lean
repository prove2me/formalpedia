-- Prove2me | solution 1 for LawvereRateDistortion.rate_distortion_le_prime_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:24:04.267234+00:00
-- url     : https://prove2.me/submissions/d7880009-13b9-4b24-96fb-6d83296e253d

import Mathlib
import Definitions.Def_Bridges_LawvereRateDistortionDuality

universe u

open LawvereRateDistortion in
theorem solution (S : Type u) [ClosureGeneratedProofSemiring S] [CoherentSpectrum S]
    (δ : ℝ) :
    proofRateDistortionAt S δ ≤ primeFreeEnergyCapacityAt S δ := by
  unfold proofRateDistortionAt primeFreeEnergyCapacityAt
  -- the capacity bounds every compatible prime energy
  have hub : ∀ p : PrimeSpectrum S, CoherentSpectrum.primeSepDist p ≤ δ →
      CoherentSpectrum.primeEnergy p ≤
        sSup (CoherentSpectrum.primeEnergy '' {p : PrimeSpectrum S |
          CoherentSpectrum.primeSepDist p ≤ δ}) :=
    fun p hp => le_csSup (CoherentSpectrum.energy_bdd_above δ) ⟨p, hp, rfl⟩
  -- so some admissible code has rate at most the capacity
  obtain ⟨C, hC, hrate⟩ := CoherentSpectrum.spectral_attainment δ _ hub
  exact (csInf_le (CoherentSpectrum.rate_bdd_below δ) ⟨C, hC, rfl⟩).trans hrate
