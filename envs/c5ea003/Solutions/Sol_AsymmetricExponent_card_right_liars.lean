-- Prove2me | solution 1 for AsymmetricExponent.card_right_liars
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:17:41.850364+00:00
-- url     : https://prove2.me/submissions/aec19501-4bab-4993-b139-1024278ada08

-- Sol generated from Cryptography/AsymmetricExponent/RevealDensity.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_pow_eq_one_units
import Theorems.Thm_AsymmetricExponent_gcd_exp_right

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
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ // v.2 ^ (p * q - 1) = 1}
      = eulerGap p q * (p - 1) := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have e : {v : (ZMod p)ˣ × (ZMod q)ˣ // v.2 ^ (p * q - 1) = 1} ≃
      (ZMod p)ˣ × {y : (ZMod q)ˣ // y ^ (p * q - 1) = 1} :=
    { toFun := fun v => (v.1.1, ⟨v.1.2, v.2⟩)
      invFun := fun w => ⟨(w.1, w.2.1), w.2.2⟩
      left_inv := fun v => by cases v; rfl
      right_inv := fun w => by obtain ⟨x, ⟨y, hy⟩⟩ := w; rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_pow_eq_one_units q,
    Nat.gcd_comm (q - 1) (p * q - 1), gcd_exp_right hp.pos hq.pos, eulerGap,
    Nat.card_eq_fintype_card, ZMod.card_units p, Nat.mul_comm]
