-- Prove2me | solution 1 for AsymmetricExponent.card_left_liars
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:17:41.265774+00:00
-- url     : https://prove2.me/submissions/cfe8cac6-ae09-46dc-9b9c-b05971a7693c

-- Sol generated from Cryptography/AsymmetricExponent/RevealDensity.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_pow_eq_one_units
import Theorems.Thm_AsymmetricExponent_gcd_exp_left

/-!
# Reveal density of the gcd variant `gcd(a^(N-1) - 1, N)`

The third experimental claim about `Q` concerns its gcd variant: for how many
bases `a` does `gcd(Q(a) - 1, N)` actually return a factor?  The measurement
reported a density tracking `g/p + g/q` with `g = gcd(p-1, q-1)`.  Here that is
proved exactly.

Main results.

* `AsymmetricExponent.gcd_reveal_left` / `gcd_reveal_right` — the arithmetic
  criterion: the gcd returns `p` exactly when `a^(N-1) ≡ 1 (mod p)` while
  `a^(N-1) ≢ 1 (mod q)`, i.e. (by `Core.lean`) when `ord_p(a) ∣ q-1` but
  `ord_q(a) ∤ p-1`.
* `AsymmetricExponent.card_left_liars` — exactly `g·(q-1)` units satisfy the
  left condition.
* `AsymmetricExponent.card_revealing` — the number of revealing units is
  `g·(q-1) + g·(p-1) - 2g²`, i.e. a fraction
  `g/(p-1) + g/(q-1) - 2g²/φ(N)` of all units: the measured `g/p + g/q` law.
-/

open AsymmetricExponent

open scoped Classical

/-! ## The arithmetic criterion -/



/-! ## Counting the revealing bases -/

variable {p q : ℕ}










open AsymmetricExponent in
theorem solution[Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ // v.1 ^ (p * q - 1) = 1}
      = eulerGap p q * (q - 1) := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have e : {v : (ZMod p)ˣ × (ZMod q)ˣ // v.1 ^ (p * q - 1) = 1} ≃
      {x : (ZMod p)ˣ // x ^ (p * q - 1) = 1} × (ZMod q)ˣ :=
    { toFun := fun v => (⟨v.1.1, v.2⟩, v.1.2)
      invFun := fun w => ⟨(w.1.1, w.2), w.1.2⟩
      left_inv := fun v => by cases v; rfl
      right_inv := fun w => by obtain ⟨⟨x, hx⟩, y⟩ := w; rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_pow_eq_one_units p,
    Nat.gcd_comm (p - 1) (p * q - 1), gcd_exp_left hp.pos hq.pos, eulerGap,
    Nat.gcd_comm (q - 1) (p - 1), Nat.card_eq_fintype_card, ZMod.card_units q]
