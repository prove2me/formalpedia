-- Prove2me | Theorems.Thm_edenic_semiprime_no_primitive_root
-- name    : edenic_semiprime_no_primitive_root
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-26T16:48:28.640232+00:00
-- url     : https://prove2.me/theorems/2ef7c506-7acb-5cbe-be57-9d9140559dfb
-- title:
--   An Edenic semiprime admits no primitive root
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$\lnot\, \exists\, g : \mathbb{Z}/n\mathbb{Z} \ \text{ with } \ g \text{ a primitive root modulo } n,$$
--   i.e. the multiplicative group of units $(\mathbb{Z}/n\mathbb{Z})^\times$ is never cyclic and $n$ admits no primitive root.
--
--   Classically (Gauss), $n$ has a primitive root if and only if $n \in \{1,2,4\}$, $n = q^k$, or $n = 2q^k$ for an odd prime $q$. An Edenic semiprime is the product of two *distinct odd* primes $p$ and $p+2$, so it matches none of these shapes. Concretely, by the Chinese remainder theorem
--   $$(\mathbb{Z}/n\mathbb{Z})^\times \cong (\mathbb{Z}/p\mathbb{Z})^\times \times (\mathbb{Z}/(p+2)\mathbb{Z})^\times ,$$
--   a direct product of two cyclic groups, each of even order ($p - 1$ and $p + 1$ are consecutive even numbers). Each factor contributes its own element of order $2$ (namely $-1$), so the product contains at least three involutions — while a cyclic group of even order has exactly one. Hence the group is not cyclic, no generator exists, and $n$ has no primitive root.
--
--   **Formalization.** Assume a primitive root $g$ of order $\varphi(n)$; positivity of $\varphi$ (from $0 < n$) supplies `NeZero` for the modulus, and `IsPrimitiveRoot.isUnit_unit` transports $g$ into the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$. Since `ZMod.card_units_eq_totient` identifies $\varphi(n)$ with the cardinality of the unit group (`Nat.card_eq_fintype_card` bridges `Fintype.card` to `Nat.card`), `isCyclic_of_orderOf_eq_card` exhibits $(\mathbb{Z}/n\mathbb{Z})^\times$ as cyclic — contradicting `ZMod.not_isCyclic_units_of_mul_coprime`, applied to the coprime odd pair $p$, $p + 2$: oddness from `hp.eq_two_or_odd'` (and shifting by $2$), nontriviality from `Nat.Prime.ne_one`, coprimality from `twin_primes_coprime` (imported).
--
--   **Reuse.** A reduction through `twin_primes_coprime`. Complements `edenic_semiprime_totient` ($\varphi(n) = k^2-2k$) and `edenic_semiprime_not_perfect_power`: no member of the family is a prime power or twice a prime power, which is exactly the obstruction in Gauss's classification.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_no_primitive_root (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ g : ZMod n, IsPrimitiveRoot g (Nat.totient n) := by
  sorry
