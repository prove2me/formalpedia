-- Prove2me | Theorems.Thm_SingularModuli_smCost_not_polyBounded
-- name    : SingularModuli.smCost_not_polyBounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T21:16:50.848069+00:00
-- url     : https://prove2.me/theorems/00c541bd-80d4-4254-82dd-2d78c77b8606
-- title:
--   Consequently the cost profile is not polynomially bounded.
-- statement:
--   Consequently the cost profile is not polynomially bounded.
--
--   ```lean
--   theorem SingularModuli.smCost_not_polyBounded(hh : 0 < h) : ¬ PolyBounded (smCost h) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SingularModuli/ExponentialRung.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SingularModuli/ExponentialRung.lean#L87

-- Thm stub generated from Cryptography/SingularModuli/ExponentialRung.lean
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_AsymptoticLadder
import Definitions.Def_Cryptography_FactoringBarriers_Capstone
import Definitions.Def_Cryptography_SingularModuli_ExponentialRung
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

/-!
# Singular Moduli Factoring, Step 4: which rung of the ladder it occupies

`SqrtBarrier.lean` proves that the expected number of evaluations of the
singular moduli method on a balanced semiprime is at least `√N / (4h)`.  In the
bit-size variable `x = log N` this is the cost function

  `smCost h x = exp (x / 2) / (4 h)`.

This file places that function on the asymptotic ladder of
`FactoringBarriers.AsymptoticLadder`:

* `smCost_superpoly`      — it is superpolynomial (no polynomial time);
* `smCost_not_subexp`     — it is a *genuine exponential*, unlike the
  smoothness/sieve barrier `L[1/3,1]`;
* `smCost_dominates_randomness` — it eventually dominates the Pollard rho
  barrier `exp (x/4)`, so singular moduli is asymptotically at least as
  expensive as rho;
* `singularModuliAlgorithm` / `singularModuli_usesClassifiedResource` — the
  method fits into the existing four-resource classification (its barrier is the
  randomness/collision rung), and therefore
* `singularModuli_not_polyTime` — its cost profile is not polynomially bounded.

Together with `Cryptography/FactoringBarriers/ResourceClassification.lean`, this
is the precise sense of the paper's claim: singular moduli factoring joins
Pollard rho and Pollard `p-1` in the `√N` family, strictly above the sieve rung.
-/

open SingularModuli

open Filter Real FactoringBarriers
open scoped Topology

/-! ## Two stability lemmas for the growth classes -/



/-! ## The singular moduli cost function -/


variable {h : ℝ}

theorem SingularModuli.smCost_not_polyBounded(hh : 0 < h) : ¬ PolyBounded (smCost h) := by sorry
