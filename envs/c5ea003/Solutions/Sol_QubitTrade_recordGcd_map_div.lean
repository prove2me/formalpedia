-- Prove2me | solution 1 for QubitTrade.recordGcd_map_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:17:00.904804+00:00
-- url     : https://prove2.me/submissions/dc625aee-3742-4cfd-ab5b-dc95f2312f5e

-- Sol generated from Algebra/QubitTrade/JordanCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_JordanCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SuccessDensity

/-!
# QUBIT-TRADE XII: the exact number of successful records

`SuccessDensity.lean` bounds the number of *good* records — the length-`m`
records of numerators whose joint gcd is coprime to the order `r`, i.e. exactly
the records that `recordEstimate` turns into the true order — from below by
`r^m / 2`.  Here we compute that number **exactly**.

The count is Jordan's totient `J_m(r)`:

* `QubitTrade.sum_card_goodRecords` — the divisor identity
  `∑_{d ∣ r} #good(d, m) = r^m`, proved by an explicit bijection that rescales a
  record by the gcd of its entries with `r`;
* `QubitTrade.card_goodRecords_eq_moebius_sum` — Möbius inversion of that
  identity: `#good(r, m) = ∑_{d ∣ r} μ(d) · (r/d)^m`;
* `QubitTrade.card_goodRecords_eq_euler_product` — the closed Euler product
  `#good(r, m) = r^m · ∏_{p ∣ r} (1 − p^{−m})`.

The last statement is the exact form of the success density conjectured in the
previous cycle: the failure probability of an `m`-sample record is exactly
`1 − ∏_{p ∣ r} (1 − p^{−m})`, which is `≤ ω(r)·2^{−m}` and `< 1/2` for `m ≥ 2`,
recovering the earlier bounds and pinning the constant.
-/

open QubitTrade

open Finset ArithmeticFunction

variable {r m : ℕ}

/-! ## Rescaling records -/









/-! ## The Euler product -/




open QubitTrade in
theorem solution{e : ℕ} :
    ∀ {L : List ℕ}, (∀ x ∈ L, e ∣ x) → recordGcd (L.map (fun x => x / e)) * e = recordGcd L := by
  intro L
  induction L with
  | nil => intro _; simp [recordGcd]
  | cons a L ih =>
      intro h
      have ha : e ∣ a := h a (by simp)
      have hL : ∀ x ∈ L, e ∣ x := fun x hx => h x (by simp [hx])
      have h1 : recordGcd ((a :: L).map (fun x => x / e))
          = Nat.gcd (a / e) (recordGcd (L.map (fun x => x / e))) := by
        simp [recordGcd]
      have h2 : recordGcd (a :: L) = Nat.gcd a (recordGcd L) := by simp [recordGcd]
      have h3 : Nat.gcd a (recordGcd L)
          = Nat.gcd (a / e * e) (recordGcd (L.map (fun x => x / e)) * e) := by
        rw [Nat.div_mul_cancel ha, ih hL]
      rw [h1, h2, h3, Nat.gcd_mul_right]
