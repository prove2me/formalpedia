-- Prove2me | solution 1 for AsymmetricExponent.card_revealing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:19:14.427411+00:00
-- url     : https://prove2.me/submissions/61df10bc-a762-41a6-8797-c3349ea8fb9b

-- Sol generated from Cryptography/AsymmetricExponent/RevealDensity.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars
import Theorems.Thm_AsymmetricExponent_card_left_liars
import Theorems.Thm_AsymmetricExponent_card_pow_eq_one_units
import Theorems.Thm_AsymmetricExponent_card_right_liars
import Theorems.Thm_AsymmetricExponent_gcd_exp_left
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



/-- Units that are liars in *both* components: `g²` of them (the Fermat liars
of `N` itself, transported through the CRT isomorphism). -/
theorem card_both_liars [Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.1 ^ (p * q - 1) = 1 ∧ v.2 ^ (p * q - 1) = 1} = (eulerGap p q) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  rw [Nat.card_congr (Equiv.subtypeProdEquivProd
      (p := fun x : (ZMod p)ˣ => x ^ (p * q - 1) = 1)
      (q := fun y : (ZMod q)ˣ => y ^ (p * q - 1) = 1)),
    Nat.card_prod, card_pow_eq_one_units p, card_pow_eq_one_units q,
    Nat.gcd_comm (p - 1) (p * q - 1), Nat.gcd_comm (q - 1) (p * q - 1),
    gcd_exp_left hp.pos hq.pos, gcd_exp_right hp.pos hq.pos, eulerGap,
    Nat.gcd_comm (q - 1) (p - 1), sq]

/-- Splitting a count along a predicate. -/
theorem card_split {α : Type*} [Fintype α] (A B : α → Prop) :
    Nat.card {x // A x ∧ B x} + Nat.card {x // A x ∧ ¬ B x} = Nat.card {x // A x} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.card_filter_add_card_filter_not _

/-- **Reveal count, one side.** The gcd variant returns the factor `p` for
exactly `g·(q-1) - g²` units. -/
theorem card_reveal_left [Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.1 ^ (p * q - 1) = 1 ∧ ¬ v.2 ^ (p * q - 1) = 1}
      = eulerGap p q * (q - 1) - (eulerGap p q) ^ 2 := by
  have h := card_split (α := (ZMod p)ˣ × (ZMod q)ˣ)
    (fun v => v.1 ^ (p * q - 1) = 1) (fun v => v.2 ^ (p * q - 1) = 1)
  rw [card_both_liars, card_left_liars] at h
  omega

/-- **Reveal count, other side.** -/
theorem card_reveal_right [Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.2 ^ (p * q - 1) = 1 ∧ ¬ v.1 ^ (p * q - 1) = 1}
      = eulerGap p q * (p - 1) - (eulerGap p q) ^ 2 := by
  have h := card_split (α := (ZMod p)ˣ × (ZMod q)ˣ)
    (fun v => v.2 ^ (p * q - 1) = 1) (fun v => v.1 ^ (p * q - 1) = 1)
  have hboth : Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
      v.2 ^ (p * q - 1) = 1 ∧ v.1 ^ (p * q - 1) = 1} = (eulerGap p q) ^ 2 := by
    rw [← card_both_liars]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
  rw [hboth, card_right_liars] at h
  omega




open AsymmetricExponent in
theorem solution[Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.1 ^ (p * q - 1) = 1 ∧ ¬ v.2 ^ (p * q - 1) = 1}
      + Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.2 ^ (p * q - 1) = 1 ∧ ¬ v.1 ^ (p * q - 1) = 1}
      = eulerGap p q * (q - 1) + eulerGap p q * (p - 1) - 2 * (eulerGap p q) ^ 2 := by
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hgq : eulerGap p q * (q - 1) ≥ (eulerGap p q) ^ 2 := by
    have : eulerGap p q ≤ q - 1 :=
      Nat.le_of_dvd (by have := hq.two_le; omega) (Nat.gcd_dvd_right _ _)
    calc (eulerGap p q) ^ 2 = eulerGap p q * eulerGap p q := sq _
      _ ≤ eulerGap p q * (q - 1) := Nat.mul_le_mul_left _ this
  have hgp : eulerGap p q * (p - 1) ≥ (eulerGap p q) ^ 2 := by
    have : eulerGap p q ≤ p - 1 :=
      Nat.le_of_dvd (by have := hp.two_le; omega) (Nat.gcd_dvd_left _ _)
    calc (eulerGap p q) ^ 2 = eulerGap p q * eulerGap p q := sq _
      _ ≤ eulerGap p q * (p - 1) := Nat.mul_le_mul_left _ this
  rw [card_reveal_left, card_reveal_right]
  omega
