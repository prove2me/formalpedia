-- Prove2me | Theorems.Thm_ZMod_kloosterman_sum_crt
-- name    : ZMod.kloosterman_sum_crt
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:07:37.766001+00:00
-- url     : https://prove2.me/theorems/5ab331bd-781a-42df-981a-5c5b850fc8dd
-- title:
--   Twisted multiplicativity of Kloosterman sums: $S(m,r;c_1c_2) = S(\alpha m,\alpha r;c_1)\,S(\beta m,\beta r;c_2)$ whenever $\alpha c_2 + \beta c_1 = 1$
-- statement:
--   Let $c_1, c_2 \ge 1$ be integers and let $\alpha, \beta \in \mathbb Z$ satisfy $\alpha c_2 + \beta c_1 = 1$ (so $c_1$ and $c_2$ are coprime, $\alpha \equiv c_2^{-1} \pmod{c_1}$ and $\beta \equiv c_1^{-1} \pmod{c_2}$). For $c \ge 1$ and $m, r \in \mathbb Z$ let
--
--   $$S(m,r;c) = \sum_{x \in (\mathbb Z/c\mathbb Z)^\times} e\!\left(\frac{m x + r \bar x}{c}\right), \qquad e(t) = e^{2\pi i t},$$
--
--   be the Kloosterman sum, where $\bar x$ is the inverse of $x$ modulo $c$. Then for all $m, r \in \mathbb Z$
--
--   $$S(m, r; c_1 c_2) = S(\alpha m, \alpha r; c_1)\, S(\beta m, \beta r; c_2).$$
--
--   Proof idea: $\frac{1}{c_1 c_2} = \frac{\alpha}{c_1} + \frac{\beta}{c_2}$, so $e\big(\frac{t}{c_1 c_2}\big) = e\big(\frac{\alpha t}{c_1}\big)\, e\big(\frac{\beta t}{c_2}\big)$, and by the Chinese remainder theorem $x \mapsto (x \bmod c_1, x \bmod c_2)$ is a bijection $(\mathbb Z/c_1c_2)^\times \to (\mathbb Z/c_1)^\times \times (\mathbb Z/c_2)^\times$ that is compatible with inverses.
--
--   For example, with $c_1 = 3$, $c_2 = 5$, $\alpha = 2$, $\beta = -3$ ($2 \cdot 5 - 3 \cdot 3 = 1$) this gives $S(m, r; 15) = S(2m, 2r; 3)\, S(-3m, -3r; 5)$.
--
--   Role: twisted multiplicativity reduces Kloosterman sums to prime-power moduli; combined with the Weil or Kloosterman bound at primes and the trivial bound at higher prime powers it bounds $S(m,r;c)$ for every modulus $c$, as needed for the convergence of Poincaré series and for the Petersson formula in weight two.
--
--   **Formalization Note**: `ZMod.stdAddChar` is Mathlib's standard additive character of `ZMod c`, $t \mapsto e^{2\pi i t/c}$, so the summand is $e((m x + r \bar x)/c)$. Each sum runs over the unit group `(ZMod c)ˣ`, and `(x : ZMod c)⁻¹` is the inverse in `ZMod c` (for a unit $x$ this is $\bar x$). The integers $m, r, \alpha m, \ldots$ enter through their images in `ZMod c` (integer casts); `NeZero c₁`, `NeZero c₂` say $c_1, c_2 \ne 0$. Coprimality is not a separate hypothesis because the Bezout relation `hab : α * c₂ + β * c₁ = 1` already forces it.
-- source:
--   H. Iwaniec, Topics in Classical Automorphic Forms, Graduate Studies in Mathematics 17, AMS 1997, Section 4.3 (Kloosterman sums); H. Iwaniec and E. Kowalski, Analytic Number Theory, AMS Colloquium Publications 53, 2004, Section 11.7

import Mathlib

set_option autoImplicit false

theorem ZMod.kloosterman_sum_crt {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] {α β : ℤ}
    (hab : α * c₂ + β * c₁ = 1) (m r : ℤ) :
    ∑ x : (ZMod (c₁ * c₂))ˣ, ZMod.stdAddChar ((m : ZMod (c₁ * c₂)) * (x : ZMod (c₁ * c₂)) +
        (r : ZMod (c₁ * c₂)) * (x : ZMod (c₁ * c₂))⁻¹) =
      (∑ x : (ZMod c₁)ˣ, ZMod.stdAddChar (((α * m : ℤ) : ZMod c₁) * (x : ZMod c₁) +
        ((α * r : ℤ) : ZMod c₁) * (x : ZMod c₁)⁻¹)) *
      (∑ x : (ZMod c₂)ˣ, ZMod.stdAddChar (((β * m : ℤ) : ZMod c₂) * (x : ZMod c₂) +
        ((β * r : ℤ) : ZMod c₂) * (x : ZMod c₂)⁻¹)) := by
  sorry
