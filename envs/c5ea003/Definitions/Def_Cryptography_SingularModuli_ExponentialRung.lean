-- Prove2me | Definitions.Def_Cryptography_SingularModuli_ExponentialRung
-- name    : Cryptography_SingularModuli_ExponentialRung
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:36:23.596032+00:00
-- url     : https://prove2.me/theorems/67fc9a7d-cee8-461d-8897-b1a35831978e
-- title:
--   Aether Catalog definitions — Cryptography_SingularModuli_ExponentialRung
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SingularModuli.ExponentialRung`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SingularModuli/ExponentialRung.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_Capstone
import Definitions.Def_Cryptography_FactoringBarriers_ResourceClassification
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

namespace SingularModuli

open Filter Real FactoringBarriers
open scoped Topology

/-! ## Two stability lemmas for the growth classes -/



/-! ## The singular moduli cost function -/

/-- The proven lower bound on the expected cost of the singular moduli method for
a balanced semiprime, in the bit-size variable `x = log N`:
`√N / (4h) = exp (x/2) / (4h)`. -/
noncomputable def smCost (h : ℝ) (x : ℝ) : ℝ := Real.exp (x / 2) / (4 * h)

variable {h : ℝ}




/-- **Singular moduli is asymptotically at least as expensive as Pollard rho.**
Eventually `exp (x/4) ≤ exp (x/2) / (4h)`: the proven `√N/(4h)` bound dominates
the `N^{1/4}` birthday bound of the collision methods. -/
theorem smCost_dominates_randomness (hh : 0 < h) :
    ∀ᶠ x in atTop, barrierCost .randomness x ≤ smCost h x := by
  have hexp : Tendsto (fun x : ℝ => Real.exp (x / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  filter_upwards [hexp.eventually_ge_atTop (4 * h)] with x hx
  have h4 : (0:ℝ) < 4 * h := by positivity
  have hsplit : Real.exp (x / 2) = Real.exp (x / 4) * Real.exp (x / 4) := by
    rw [← Real.exp_add]; ring_nf
  show Real.exp (1 / 4 * x) ≤ Real.exp (x / 2) / (4 * h)
  rw [le_div_iff₀ h4, hsplit, show (1:ℝ) / 4 * x = x / 4 by ring]
  exact mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le


/-! ## Fitting the method into the four-resource classification -/

/-- The singular moduli method, abstracted to its proven cost profile. -/
noncomputable def singularModuliAlgorithm (hh : 0 < h) : ClassicalAlgorithm where
  cost := smCost h
  one_le_cost := by
    have hexp : Tendsto (fun x : ℝ => Real.exp (x / 4)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
    filter_upwards [smCost_dominates_randomness hh,
      hexp.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have : (1:ℝ) ≤ barrierCost .randomness x := by
      show (1:ℝ) ≤ Real.exp (1 / 4 * x)
      rw [show (1:ℝ) / 4 * x = x / 4 by ring]
      exact hx1
    linarith




end SingularModuli


