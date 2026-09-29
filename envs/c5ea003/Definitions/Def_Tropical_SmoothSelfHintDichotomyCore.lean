-- Prove2me | Definitions.Def_Tropical_SmoothSelfHintDichotomyCore
-- name    : Tropical_SmoothSelfHintDichotomyCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:45.968234+00:00
-- url     : https://prove2.me/theorems/8f85d848-4e29-4d74-bc16-49d8495923c3
-- title:
--   Aether Catalog definitions — Tropical_SmoothSelfHintDichotomyCore
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SmoothSelfHintDichotomyCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SmoothSelfHintDichotomyCore.lean by skeleton subtraction
import Mathlib

/-!
# The asymmetric / symmetric divisibility dichotomy

Motivation (Paper 54, Experiment 389).  For a semiprime `N = p * q` and a small prime
`l`, one asks whether `N` "knows" something about the divisibility of `p - 1` by `l`
(the elementary building block of `p - 1`/ECM smoothness).  The experiment reports

* `I(N mod l ; l ∣ p-1) = 0` (asymmetric event: zero leak),
* `I(N mod l ; l ∣ p-1 ∨ l ∣ q-1) > 0` (symmetric event: strong leak, `0.313` bits at
  `l = 3`), with an exact mechanism at `l = 3`: `N ≡ 2 (mod 3)` *forces* one factor to
  be `≡ 1 (mod 3)`.

This file proves the structural reason, in complete generality, as a statement about
fibres of the multiplication map of a finite group `G` (for us `G = (ZMod l)ˣ`):

* `SmoothSelfHint.asym_fiber_card` : for **any** `A ⊆ G` and **any** `n`, the number of
  pairs `(a,b)` with `a * b = n` and `a ∈ A` equals `|A|` — independent of `n`.
  One–sided ("asymmetric") events are *exactly* independent of the product.
* `SmoothSelfHint.sym_fiber_card` : the two–sided ("symmetric") count is
  `|A ∪ n·A⁻¹|`, which genuinely depends on `n`.
* `SmoothSelfHint.sym_fiber_card_one` : for the singleton `A = {1}` the symmetric count
  is `1` if `n = 1` and `2` otherwise — the whole leak, in one line.
* `SmoothSelfHint.asym_condProb_constant` / `SmoothSelfHint.sym_condProb_not_constant`:
  the resulting conditional probabilities, `1/(l-1)` versus `(1 or 2)/(l-1)`.

The arithmetic half of the file turns this into statements about actual semiprimes:

* `SmoothSelfHint.symmetric_forced_mod_three` : the exact `l = 3` mechanism.
* `SmoothSelfHint.asym_not_residue_dial` : no function of `N mod 3` computes `3 ∣ p-1`,
  and indeed *both* residue classes carry both outcomes.
* `SmoothSelfHint.sym_not_forced_mod_five` : at `l = 5` even the symmetric event is not
  forced — the leak there is purely statistical (`0.036` bits), as measured.
-/

open Finset

namespace SmoothSelfHint

/-! ## Part 1 : fibres of multiplication in a finite group -/

section Group

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The fibre of the multiplication map over `n`, intersected with a one–sided
("asymmetric") condition on the first coordinate. -/
def asymFiber (A : Finset G) (n : G) : Finset (G × G) :=
  (Finset.univ : Finset (G × G)).filter (fun ab => ab.1 * ab.2 = n ∧ ab.1 ∈ A)

/-- The fibre of the multiplication map over `n`, intersected with the two–sided
("symmetric") condition that *some* coordinate lies in `A`. -/
def symFiber (A : Finset G) (n : G) : Finset (G × G) :=
  (Finset.univ : Finset (G × G)).filter
    (fun ab => ab.1 * ab.2 = n ∧ (ab.1 ∈ A ∨ ab.2 ∈ A))







end Group

/-! ## Part 2 : the conditional probabilities for `G = (ZMod l)ˣ` -/

section ZMod

variable (l : ℕ) [Fact (Nat.Prime l)]



/-- Conditional probability of the *asymmetric* event `a = 1` given `a * b = n`. -/
def asymCondProb (n : (ZMod l)ˣ) : ℚ :=
  ((asymFiber ({1} : Finset (ZMod l)ˣ) n).card : ℚ) / (Fintype.card (ZMod l)ˣ : ℚ)

/-- Conditional probability of the *symmetric* event `a = 1 ∨ b = 1` given `a * b = n`. -/
def symCondProb (n : (ZMod l)ˣ) : ℚ :=
  ((symFiber ({1} : Finset (ZMod l)ˣ) n).card : ℚ) / (Fintype.card (ZMod l)ˣ : ℚ)




end ZMod

/-! ## Part 3 : arithmetic incarnation for genuine semiprimes -/






end SmoothSelfHint


