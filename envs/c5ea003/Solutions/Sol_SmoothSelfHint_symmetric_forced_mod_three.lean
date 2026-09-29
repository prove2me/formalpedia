-- Prove2me | solution 1 for SmoothSelfHint.symmetric_forced_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:05.407977+00:00
-- url     : https://prove2.me/submissions/c424fc5f-d090-44f4-ab65-4c650748b361

-- Sol generated from Tropical/SmoothSelfHintDichotomyCore.lean
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










/-! ## Part 2 : the conditional probabilities for `G = (ZMod l)ˣ` -/


variable (l : ℕ) [Fact (Nat.Prime l)]









/-! ## Part 3 : arithmetic incarnation for genuine semiprimes -/







open SmoothSelfHint in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : p ≠ 3) (hq3 : q ≠ 3) (h : (p * q) % 3 = 2) :
    3 ∣ p - 1 ∨ 3 ∣ q - 1 := by
  have hpm : p % 3 ≠ 0 := by
    intro hc
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hc)
    omega
  have hqm : q % 3 ≠ 0 := by
    intro hc
    have := hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero hc)
    omega
  have hp1 : 2 ≤ p := hp.two_le
  have hq1 : 2 ≤ q := hq.two_le
  have hmul : (p * q) % 3 = ((p % 3) * (q % 3)) % 3 := Nat.mul_mod p q 3
  have hpr : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hqr : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hpr with h1 | h1 <;> rcases hqr with h2 | h2 <;> rw [h1, h2] at hmul <;>
    simp at hmul <;> omega
