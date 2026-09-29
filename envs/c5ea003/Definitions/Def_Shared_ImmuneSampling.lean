-- Prove2me | Definitions.Def_Shared_ImmuneSampling
-- name    : Shared_ImmuneSampling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:03:08.833076+00:00
-- url     : https://prove2.me/theorems/ce6da793-d968-4df5-82e8-28f499c58182
-- title:
--   Aether Catalog definitions — Shared_ImmuneSampling
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ImmuneSampling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ImmuneSampling.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_ImmuneAstCore
import Definitions.Def_Shared_ImmuneBounded
import Definitions.Def_Shared_ImmuneQuarantine

/-!
# Algorithmic Immune System, Part IX: monitoring frequency and periodic self-healing

Part IV assumed the monitor verifies attestation after *every* mutation step.
Real immune systems sample: they verify every `k` steps.  This part determines
exactly what is lost.

`traceK S b adv k` is the guarded run in which quarantine is applied only at
times divisible by `k`.  We prove:

* `traceK_one` — with `k = 1` sampled monitoring *is* the continuous monitoring of
  Part IV, so containment and neutralization hold verbatim;
* `periodic_healing` — for any `k` and any adversary the system is sanctioned at
  every checkpoint: damage is always repaired within one period (self-healing);
* `sampling_gap` — but for `k ≥ 2` there is an adversary and a time at which the
  forbidden action *is* executed: no relaxation of the sampling rate is safe;
* `attack_window` — worse, the adversary keeps the system compromised at every
  non-checkpoint time, so the fraction of compromised steps is `(k-1)/k`;
* `monitoring_frequency_dichotomy` — continuous monitoring is therefore both
  necessary and sufficient for total containment.
-/

namespace ImmuneSystem
namespace PAst

/-- The sampled guarded run: the adversary mutates at every step, the monitor
verifies and rolls back only at times divisible by `k`. -/
def traceK (S : Finset PAst) (b : PAst) (adv : ℕ → PAst → PAst) (k : ℕ) : ℕ → PAst
  | 0 => b
  | n + 1 =>
      if (n + 1) % k = 0 then quarantine S b (adv n (traceK S b adv k n))
      else adv n (traceK S b adv k n)








end PAst
end ImmuneSystem


