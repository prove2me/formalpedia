-- Prove2me | Theorems.Thm_RLHF_vonMangoldt_strict_improvement
-- name    : RLHF.vonMangoldt_strict_improvement
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:49:59.184421+00:00
-- url     : https://prove2.me/theorems/20b60bef-fd90-4a32-af1e-ddd34e096994
-- title:
--   The primes power the alignment gain.
-- statement:
--   **The primes power the alignment gain.**  For `N ≥ 2` the von Mangoldt reward is
--   non-constant on `{1, …, N}` (since `Λ 1 = 0 < log 2 = Λ 2`), so KL-regularized RLHF
--   *strictly* improves upon the uniform SFT reference at every temperature.
--
--   ```lean
--   theorem RLHF.vonMangoldt_strict_improvement{β : ℝ} {N : ℕ} (hβ : 0 < β) (hN : 2 ≤ N) :
--       haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
--       chebyshevPsiFin N / (N : ℝ) < freeEnergy β (vonMangoldtReward N) (unifRef N) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/RLHFTemperatureSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/RLHFTemperatureSpectrum.lean#L158

-- Thm stub generated from NumberTheory/RLHFTemperatureSpectrum.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# The RLHF free-energy spectrum and a von Mangoldt reward model

Building on `NumberTheory.RLHFGibbsVariational`, we study the *free energy*
`V(β) = β log Z(β)`, which by the Gibbs variational principle is the optimal value of
the KL-regularized RLHF objective at temperature `β`.

Main results:

* `RLHF.freeEnergy_antitone` — `V` is antitone in the KL coefficient `β`:
  stronger regularization can only lower the achievable value.
* `RLHF.freeEnergy_le_of_le` — `V(β) ≤ sup r` (no reward hacking beyond the reward ceiling).
* `RLHF.freeEnergy_ge_reference` — `V(β) ≥ 𝔼_p[r]` (RLHF never hurts).
* `RLHF.gibbs_ne_reference_of_nonconstant` and `RLHF.strict_improvement` — RLHF strictly
  improves on the SFT reference exactly when the reward model is non-constant.
* Number-theoretic instantiation: reward `r(n) = Λ(n)` (von Mangoldt) on the response
  space `{1, …, N}` with the uniform SFT reference.  Then the free energy is squeezed,
  `ψ(N)/N ≤ V(β) ≤ log N` (`RLHF.vonMangoldt_freeEnergy_ge_chebyshev`,
  `RLHF.vonMangoldt_freeEnergy_le_log`), and for `N ≥ 2` the lower bound is *strict*
  (`RLHF.vonMangoldt_strict_improvement`): the alignment gain is powered exactly by the
  irregularity of the primes.
-/

open RLHF

open Finset ArithmeticFunction

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]








/-! ## The von Mangoldt reward model on `{1, …, N}` -/

theorem RLHF.vonMangoldt_strict_improvement{β : ℝ} {N : ℕ} (hβ : 0 < β) (hN : 2 ≤ N) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
    chebyshevPsiFin N / (N : ℝ) < freeEnergy β (vonMangoldtReward N) (unifRef N) := by sorry
