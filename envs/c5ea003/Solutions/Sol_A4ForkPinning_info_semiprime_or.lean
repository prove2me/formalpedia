-- Prove2me | solution 1 for A4ForkPinning.info_semiprime_or
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:23:18.587274+00:00
-- url     : https://prove2.me/submissions/1c407b8e-f688-4010-afb6-01071da9603a

-- Sol generated from Algebra/A4ForkPinning/Semiprime.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_Resolvent
import Definitions.Def_Algebra_A4ForkPinning_Semiprime
import Theorems.Thm_A4ForkPinning_hb_symm
/-
# The order-3 channel on a non-abelian field: semiprime level

`N = p·q` with `p, q` unramified.  The dial is again the residue `N mod 9`; since
the cubic character is multiplicative (`chi9_mul`), the dial sees only the *sum*
`s = chi9(p) + chi9(q) ∈ ℤ/3` of the two cube classes, which are independent and
uniform (Chebotarev for the `A₄`-field, Dirichlet for the classes).

All the observables of the experiment are computed here **exactly**:

* `A4ForkPinning.info_semiprime_and` — `I(N mod 9 ; both split) = H(1/9) - (1/3)H(1/3)`
  (`= 0.1972…`, measured `0.1997`) — again an instance of the leakage law;
* `A4ForkPinning.info_semiprime_or`  — `I(N mod 9 ; some split) = H(5/9) - H(1/3)`
  (`= 0.0728…`, measured `0.0688`);
* `A4ForkPinning.info_semiprime_xor` — `I(N mod 9 ; exactly one) = H(4/9) - (2/3)H(1/3)`
  (`= 0.3789…`, measured `0.3736`);
* `A4ForkPinning.info_semiprime_split_count` — `I(N mod 9 ; #split) = H(4/9,4/9,1/9) - H(1/3)`
  (`= 0.4739…`, measured `0.4710`), the paper-74 order-3 split-count law, here on a
  **non-abelian** field;
* `A4ForkPinning.info_semiprime_which_factor` — **the which-factor wall**: the dial
  carries *exactly zero* bits about which of the two factors split.

Every conditional rate used below is justified by an exact count of pairs
(`and_rate_eq_count` etc.), not postulated.
-/

open A4ForkPinning

open Finset

/-! ## The dial of a semiprime -/


/-! ## Counting pairs of cube classes -/














/-! ## Conditional rates -/












/-! ## Exact information laws -/






/-! ## The split-count channel -/






open A4ForkPinning in
theorem solution: info w3 orRate = hb (5 / 9) - hb (1 / 3) := by
  have havg : avg w3 orRate = 5 / 9 := by
    simp [avg, w3, orRate, Fin.sum_univ_three]; norm_num
  have hsymm : hb (2 / 3) = hb (1 / 3) := by
    have := hb_symm (1 / 3 : ℝ)
    rwa [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num] at this
  have hcond : condEntropy w3 orRate = hb (1 / 3) := by
    simp only [condEntropy, w3, orRate, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    rw [hsymm]
    ring
  rw [info, havg, hcond]
