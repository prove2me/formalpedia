-- Prove2me | Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
-- name    : Speculative_AutoResearch_TraceBatteryEntropy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:31:48.330604+00:00
-- url     : https://prove2.me/theorems/34886dfe-bce3-4cdc-89a8-f75ecb967c93
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_TraceBatteryEntropy
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.TraceBatteryEntropy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/TraceBatteryEntropy.lean by skeleton subtraction
import Mathlib
/-
# TRACE-BATTERY, part I: an exact finitary Shannon calculus

Companion to the round-30 experiment `TRACE-BATTERY` (paper 108), whose numeric
claim is that the *joint channel capacity* of a battery of arithmetic "dials"
grows as dials are added, staying under the CRT ceiling `log₂ M` and under the
sample ceiling `log₂ N`.

Mathlib (v4.28.0) has no general Shannon entropy, so this file builds the
finitary theory that the experiment's book-keeping silently uses.  For a finite
population `Ω` and a statistic `f : Ω → α` we define the *empirical entropy*

  `H f = ∑_{a ∈ image f} (nₐ/N) · log (N/nₐ)`,   `nₐ = #f⁻¹(a)`, `N = #Ω`,

i.e. the Shannon entropy of the push-forward of the uniform measure on `Ω`.
Because a dial reading is a *deterministic* function of the individual, this is
exactly the mutual information `I(individual ; reading)` the experiment reports.

The results proved here, all sorry-free:

* `TraceBattery.H_nonneg` — capacities are non-negative.
* `TraceBattery.H_le_log_card_img` — **max-entropy / alphabet ceiling**,
  `H f ≤ log #(image f)`; proved by the Gibbs estimate `log x ≤ x - 1`.
* `TraceBattery.H_le_log_card` — **sparse-table bias**: `H f ≤ log N`.  A
  capacity read off a table with `N` rows can never exceed `log₂ N` bits,
  whatever the alphabet.
* `TraceBattery.H_comp_le` — **data processing**: post-processing a statistic
  cannot increase its capacity, `H (g ∘ f) ≤ H f`.
* `TraceBattery.H_comp_eq_of_injective` — relabelling is free.
* `TraceBattery.H_pos_of_ne` — a statistic separating two individuals has
  strictly positive capacity.
* `TraceBattery.H_pair_le` — **subadditivity** `H⟨f,g⟩ ≤ H f + H g`.

Everything is stated in nats (`Real.log`); the bit-valued capacity
`TraceBattery.Hb = H / log 2` used by the experiment is introduced at the end.
-/

namespace TraceBattery

open Finset Real

section Entropy

variable {Ω : Type*} [Fintype Ω] {α β : Type*}

open Classical in
/-- The fibre of `f` over `a`, as a finset of the population. -/
noncomputable def fib (f : Ω → α) (a : α) : Finset Ω := univ.filter (fun x => f x = a)

/-- The number of individuals with reading `a`. -/
noncomputable def cnt (f : Ω → α) (a : α) : ℕ := (fib f a).card

open Classical in
/-- The set of readings actually attained. -/
noncomputable def img (f : Ω → α) : Finset α := univ.image f







/-- **Empirical Shannon entropy** (in nats) of a statistic `f` on a finite
population: the entropy of the distribution of readings under the uniform
measure.  As readings are deterministic, this is the mutual information between
an individual and its reading. -/
noncomputable def H (f : Ω → α) : ℝ :=
  ∑ a ∈ img f, (cnt f a / (Fintype.card Ω : ℝ)) * Real.log ((Fintype.card Ω : ℝ) / cnt f a)
















end Entropy

section Subadditivity

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] {α β : Type*}



end Subadditivity

section Bits

variable {Ω : Type*} [Fintype Ω] {α : Type*}

/-- Capacity measured in **bits**, the unit used in the experiment's tables. -/
noncomputable def Hb (f : Ω → α) : ℝ := H f / Real.log 2




end Bits

end TraceBattery


