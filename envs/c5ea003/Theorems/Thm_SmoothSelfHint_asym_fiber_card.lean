-- Prove2me | Theorems.Thm_SmoothSelfHint_asym_fiber_card
-- name    : SmoothSelfHint.asym_fiber_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:18.253485+00:00
-- url     : https://prove2.me/theorems/15ff041a-d981-4c7e-807f-222d8acc8a90
-- title:
--   Asymmetric invisibility.
-- statement:
--   **Asymmetric invisibility.**  The number of factorisations `n = a * b` with the
--   first factor in `A` is `|A|`, whatever `n` is.  Equivalently: the event `a ∈ A` is
--   statistically independent of the product `a * b`.
--
--   ```lean
--   theorem SmoothSelfHint.asym_fiber_card(A : Finset G) (n : G) : (asymFiber A n).card = A.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SmoothSelfHintDichotomyCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SmoothSelfHintDichotomyCore.lean#L57

-- Thm stub generated from Tropical/SmoothSelfHintDichotomyCore.lean
import Mathlib
import Definitions.Def_Tropical_SmoothSelfHintDichotomyCore

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

open SmoothSelfHint

/-! ## Part 1 : fibres of multiplication in a finite group -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

theorem SmoothSelfHint.asym_fiber_card(A : Finset G) (n : G) : (asymFiber A n).card = A.card := by sorry
