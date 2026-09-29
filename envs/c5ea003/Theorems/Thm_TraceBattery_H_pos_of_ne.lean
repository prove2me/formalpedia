-- Prove2me | Theorems.Thm_TraceBattery_H_pos_of_ne
-- name    : TraceBattery.H_pos_of_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:13.403151+00:00
-- url     : https://prove2.me/theorems/5b20b51b-1046-4c2a-a1b2-65becc659c62
-- title:
--   A statistic that separates two individuals has strictly positive capacity.
-- statement:
--   A statistic that separates two individuals has strictly positive capacity.
--
--   ```lean
--   theorem TraceBattery.H_pos_of_ne[Nonempty Ω] {f : Ω → α} {x y : Ω} (hxy : f x ≠ f y) : 0 < H f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/TraceBatteryEntropy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/TraceBatteryEntropy.lean#L352

-- Thm stub generated from Speculative/AutoResearch/TraceBatteryEntropy.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TraceBatteryEntropy
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

open TraceBattery

open Finset Real


variable {Ω : Type*} [Fintype Ω] {α β : Type*}

theorem TraceBattery.H_pos_of_ne[Nonempty Ω] {f : Ω → α} {x y : Ω} (hxy : f x ≠ f y) : 0 < H f := by sorry
