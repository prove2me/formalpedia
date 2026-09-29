-- Prove2me | Theorems.Thm_Round11_mobRaw_eq_of_lt_dstar
-- name    : Round11.mobRaw_eq_of_lt_dstar
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:30:00.291226+00:00
-- url     : https://prove2.me/theorems/3ed8c428-fd0d-4631-a990-854cc3f872e0
-- title:
--   **The `N`-computable Möbius coefficients are instance-independent below the
-- statement:
--   **The `N`-computable Möbius coefficients are instance-independent below the
--   order scale.**  For `0 < d < d*` the coefficient `M_d` equals `[d = 1]` — the
--   same value for every semiprime and every base.  This is CIFINGER in the form the
--   attacker actually has access to.
--
--   ```lean
--   theorem Round11.mobRaw_eq_of_lt_dstar{p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       (hb : 1 ≤ b) (hd : 0 < d) (hlt : d < min (ordAt b p) (ordAt b q)) :
--       mobRaw b (p * q) d = if d = 1 then 1 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Round11CycleIndexFingerprint.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Round11CycleIndexFingerprint.lean#L257

-- Thm stub generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
/-
# Round-11 Closures, Part I: the cycle-index fingerprint and its Möbius spectrum

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypotheses **CIFINGER** / **CFSIGMA**).

For a semiprime `N = p * q` and a base `b` coprime to `N`, the *cycle-index
fingerprint* is
```
F(c) = gcd (b ^ c - 1) N .
```
The paper asserts three things about it, all of which are proved here in full:

* **Structure.** `F(c) = p^[ord_p b ∣ c] * q^[ord_q b ∣ c]`
  (`Round11.fpr_eq_indicator`).
* **The order seal.** `F(c) = 1` for every `0 < c < min (ord_p b) (ord_q b)`, and
  `F` first becomes informative exactly at `d* = min (ord_p b) (ord_q b)`
  (`Round11.fpr_eq_one_of_lt_dstar`, `Round11.one_lt_fpr_dstar`).
* **The Möbius spectrum.** The Möbius transform of the `p`-adic valuation of the
  fingerprint is the *exact indicator of the multiplicative order*:
  `∑_{c ∣ d} μ(d/c) · v_p(F c) = [ord_p b = d]`
  (`Round11.mobFinger_eq_indicator`).  Consequently the Möbius spectrum is
  supported on the two-element set `{ord_p b, ord_q b}`
  (`Round11.mobFinger_eq_zero_of_lt_dstar`): the Möbius structure is genuine but
  relocates no information below the order scale.

The last consequence is the formal content of the CFSIGMA closure: below the
order scale the fingerprint is a *constant* function of the instance, hence its
fibres cannot separate any secret statistic (see Part III).
-/

open Round11

open ArithmeticFunction Finset

/-! ## The fingerprint -/



/-! ## Basic arithmetic of the fingerprint -/





/-! ## The order seal: no information below `d* = min (ord_p b) (ord_q b)` -/





/-! ## The Möbius spectrum -/

theorem Round11.mobRaw_eq_of_lt_dstar{p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hd : 0 < d) (hlt : d < min (ordAt b p) (ordAt b q)) :
    mobRaw b (p * q) d = if d = 1 then 1 else 0 := by sorry
