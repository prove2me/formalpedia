-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Semiprime
-- name    : Algebra_A4ForkPinning_Semiprime
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:04:31.159816+00:00
-- url     : https://prove2.me/theorems/82115814-2203-4ed6-ae6b-ac7b4ad6c610
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Semiprime
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Semiprime`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Semiprime.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_Resolvent
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

namespace A4ForkPinning

open Finset

/-! ## The dial of a semiprime -/


/-! ## Counting pairs of cube classes -/

/-- The three possible classes of `N = pq`. -/
def cls : Fin 3 → ZMod 3 := ![0, 1, 2]

/-- Pairs of classes with prescribed sum, and both factors split. -/
def countAnd (t : ZMod 3) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 => ab.1 + ab.2 = t ∧ ab.1 = 0 ∧ ab.2 = 0)).card

/-- Pairs of classes with prescribed sum, and at least one factor split. -/
def countOr (t : ZMod 3) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 => ab.1 + ab.2 = t ∧ (ab.1 = 0 ∨ ab.2 = 0))).card

/-- Pairs of classes with prescribed sum, and exactly one factor split. -/
def countXor (t : ZMod 3) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 =>
    ab.1 + ab.2 = t ∧ ((ab.1 = 0 ∧ ab.2 ≠ 0) ∨ (ab.1 ≠ 0 ∧ ab.2 = 0)))).card

/-- Pairs of classes with prescribed sum, and the *first* factor split. -/
def countFirst (t : ZMod 3) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 => ab.1 + ab.2 = t ∧ ab.1 = 0)).card

/-- Pairs of classes with prescribed sum. -/
def countAll (t : ZMod 3) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 => ab.1 + ab.2 = t)).card

/-- Pairs with prescribed sum and prescribed number of split factors. -/
def countSplit (t : ZMod 3) (k : ℕ) : ℕ :=
  (univ.filter (fun ab : ZMod 3 × ZMod 3 => ab.1 + ab.2 = t ∧
    ((if ab.1 = 0 then 1 else 0) + (if ab.2 = 0 then 1 else 0) : ℕ) = k)).card







/-! ## Conditional rates -/

/-- Uniform distribution of the class of `N`. -/
noncomputable def w3 : Fin 3 → ℝ := fun _ => 1 / 3



/-- `P(both factors split | class of N)`. -/
noncomputable def andRate : Fin 3 → ℝ := ![1 / 3, 0, 0]

/-- `P(at least one factor splits | class of N)`. -/
noncomputable def orRate : Fin 3 → ℝ := ![1 / 3, 2 / 3, 2 / 3]

/-- `P(exactly one factor splits | class of N)`. -/
noncomputable def xorRate : Fin 3 → ℝ := ![0, 2 / 3, 2 / 3]

/-- `P(the first factor splits | class of N)`. -/
noncomputable def firstRate : Fin 3 → ℝ := fun _ => 1 / 3





/-! ## Exact information laws -/






/-! ## The split-count channel -/

/-- Conditional distribution of the number of split factors, given the class of `N`. -/
noncomputable def splitDist : Fin 3 → Fin 3 → ℝ :=
  ![![2 / 3, 0, 1 / 3], ![1 / 3, 2 / 3, 0], ![1 / 3, 2 / 3, 0]]




end A4ForkPinning


