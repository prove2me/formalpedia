-- Prove2me | Theorems.Thm_MukaiTameness_mukaiOrder_tame
-- name    : MukaiTameness.mukaiOrder_tame
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:08:57.093035+00:00
-- url     : https://prove2.me/theorems/aa3e1a67-0b37-4603-b0e7-026c8b7bcd26
-- title:
--   MukaiOrder tame
-- statement:
--   Formal statement of `MukaiTameness.mukaiOrder_tame` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MukaiTameness.mukaiOrder_tame(p : ℕ) (hp : p.Prime) (hp11 : 11 < p)
--       (N : ℕ) (hN : N ∈ mukaiOrders) : ¬ p ∣ N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MukaiTameness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MukaiTameness.lean#L85

-- Thm stub generated from Novelty/MukaiTameness.lean
import Mathlib
import Definitions.Def_Novelty_MukaiTameness
/-
# Tameness of the Mukai maximal symplectic groups in characteristic `p > 11`

The conjecture of Ohashi–Schütt type concerns the superspecial K3 surface in characteristic `p > 11`
whose symplectic automorphism group `G_s` is *maximal* — by Mukai's theorem these maximal groups form
a finite list of `11` groups, and Ohashi–Schütt show the same list governs the characteristic-`p`
picture precisely when `p` is large.  The arithmetic reason the threshold is `p > 11` is **tameness**:
the orders of all `11` Mukai groups have only the primes `2, 3, 5, 7` as factors, so for any prime
`p > 11` (indeed `p ≥ 11`) the symplectic order is prime to `p`.

The `11` Mukai maximal symplectic groups and their orders are:

| group       | order |
|-------------|-------|
| `M₂₀`       | `960` |
| `F₃₈₄`      | `384` |
| `A₄,₄`      | `288` |
| `T₁₉₂`      | `192` |
| `H₁₉₂`      | `192` |
| `N₇₂`       | `72`  |
| `M₉`        | `72`  |
| `T₄₈`       | `48`  |
| `L₂(7)`     | `168` |
| `A₆`        | `360` |
| `S₅`        | `120` |

Main results:

* `mukaiOrder_dvd_lcm` — every Mukai order divides `40320 = 2⁷·3²·5·7` (their least common multiple).
* `mukaiOrder_prime_factor_le_seven` — every prime factor of every Mukai order is `≤ 7`.
* `mukaiOrder_tame` — for every prime `p > 11` and every Mukai order `N`, `p ∤ N`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `p > 11` threshold in the K3 conjecture is *arithmetic*, not geometric:
it should be exactly the statement that no Mukai group order is divisible by a prime `> 11`.  Bolder:
the bound is even `≤ 7`, i.e. the Mukai orders are `{2,3,5,7}`-numbers, so `p > 7` already suffices for
tameness and the genuine geometric obstruction must account for the gap between `7` and `11`.

Experiment (Experimenter): list the `11` orders and compute their lcm `= 40320 = 2⁷·3²·5·7`
(`#eval` confirms `Nat.lcm` of the list is `40320` and `Nat.primeFactors 40320 = {2,3,5,7}`).  Then
`mukaiOrder_dvd_lcm` (each order divides the lcm) reduces tameness to the prime factorisation of a
single number, proved with `Nat.mem_primeFactors` and `fin_cases`.

Analysis (Analyst): tameness is genuinely arithmetic and uniform — it is the lcm `40320` whose prime
support `{2,3,5,7}` controls everything.  The experiment also surfaces the subtlety: arithmetic alone
gives `p > 7`, while the conjecture needs `p > 11`; the extra room `8,9,10,11` is where the *geometric*
rigidity (no non-trivial non-symplectic extension) must live, sharpening the future direction.

Critique (Critic): is `mukaiOrder_tame` `decide`-only?  No — it factors through the structural lemma
`mukaiOrder_dvd_lcm` and the membership characterisation of prime factors, with `fin_cases` over the
list; the prime-divisibility step is genuine `Nat` reasoning, not a single opaque `decide`.

Synthesis (PI): the `p > 11` hypothesis is anchored to the explicit lcm `40320`; combined with the
characteristic-`p` tameness of the *non-symplectic* index (in `SuperspecialK3Symplectic`), the full
automorphism order `#G = #G_s · [G:G_s]` is prime to `p`, the tameness that the classification rests on.
-/

open MukaiTameness



/-
Every Mukai order divides `40320 = 2⁷·3²·5·7`.
-/

/-
Every prime factor of every Mukai order is at most `7`.
-/

/-
**Tameness.**  For every prime `p > 11` and every Mukai maximal symplectic group order `N`,
`p` does not divide `N`.  This is the arithmetic content of the `p > 11` hypothesis: the symplectic
order is prime to the characteristic.
-/

theorem MukaiTameness.mukaiOrder_tame(p : ℕ) (hp : p.Prime) (hp11 : 11 < p)
    (N : ℕ) (hN : N ∈ mukaiOrders) : ¬ p ∣ N := by sorry
