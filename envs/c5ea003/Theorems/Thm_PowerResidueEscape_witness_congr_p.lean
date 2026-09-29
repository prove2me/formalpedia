-- Prove2me | Theorems.Thm_PowerResidueEscape_witness_congr_p
-- name    : PowerResidueEscape.witness_congr_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:43:31.922663+00:00
-- url     : https://prove2.me/theorems/e7034001-21b1-4f96-824e-54580e28bac3
-- title:
--   The two quartic witnesses are congruent modulo every divisor of `720720`.
-- statement:
--   The two quartic witnesses are congruent modulo every divisor of `720720`.
--
--   ```lean
--   theorem PowerResidueEscape.witness_congr'{M : ℕ} (hM : M ∣ 720720) : (137 : ℕ) % M = 720857 % M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/PowerResidueCircularity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/PowerResidueCircularity.lean#L185

-- Thm stub generated from Combinatorics/PowerResidueCircularity.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_PowerResidueCriterion
/-
# The higher-power reciprocity channel is not a residue dial — and buys nothing

Formal companion to `39_PowerResidue_Circularity.md` (experiment KPOWER, #374),
building on `Combinatorics.PowerResidueCriterion` (the `k`-th power criterion)
and on `Combinatorics.DialThresholdNoAmplification` (the `Dial` calculus).

**The question.**  The quadratic channel of the free-witness programme is a
*dial*: `p ↦ (D | p)` is periodic in `p`, of conductor `4|D|`
(`DialThreshold.kron`), and therefore — by the DIAL-THRESHOLD dichotomy — either
hint-computable or informative, never both.  Cubic and quartic residue symbols
are supposed to *escape* this: cubic residuacity of `2` is governed by
`4p = A² + 27B²`, which is not a congruence condition on `p`.  Does the escape
give the attacker anything?

**What is proved here.**

* `PowerResidueEscape.quadratic_two_is_dial`,
  `PowerResidueEscape.legendre_eq_kron` — the quadratic channel really *is* a
  dial: quadratic residuacity of `2` is read off `p % 8`, and for every base the
  Legendre symbol is the reading of the catalog's Kronecker dial.
* `PowerResidueEscape.cubic_two_not_periodic`,
  `PowerResidueEscape.cubic_two_not_dial` — the cubic channel is **not** a dial
  of any conductor dividing `720720 = lcm(1,…,16)`.  Witness pair:
  `43` and `720763 = 43 + 720720`, both `≡ 1 (mod 3)`, with `2` a cube mod `43`
  (`20³ ≡ 2`) and a non-cube mod `720763` (`2^240254 ≡ 632375 ≢ 1`).  In
  particular (`cubic_two_not_periodic_of_le`) no modulus `M ≤ 16` decides cubic
  residuacity of `2`.
* `PowerResidueEscape.quartic_two_not_dial` — the same for the quartic channel,
  witnessed by `137` and `720857 = 137 + 720720` (`96769⁴ ≡ 2 (mod 720857)`,
  while `2^34 ≡ 136 ≢ 1 (mod 137)`).
* `PowerResidueEscape.escape_but_no_gain` — the punchline, assembling the two
  halves: the cubic channel escapes every `720720`-conductor dial, yet its
  fingerprints obey *exactly* the quadratic capacity bound `2 ^ K`
  (`PowerResidue.card_le_two_pow_of_injOn`), so pinning `C` candidates still
  costs `K ≥ log₂ C` symbols.  Escape from periodicity ≠ extra information.
* `PowerResidueEscape.cubic_bit_needs_the_exponent` — circularity, in the form
  the experiment states it: the residue of `p` modulo the full dial modulus
  `720720` does **not** determine the cubic bit, so the only route to the bit is
  the exponent `(p-1)/3` — which presupposes `p`.

## Lab notes (real data from the KPOWER runs)

*Escape witnesses* (`p ≡ q mod 720720`, both `≡ 1 mod 3`, opposite cubic bits):

| p | p mod 720720 | 2^((p-1)/3) mod p | 2 a cube mod p? |
|---|---|---|---|
| 43 | 43 | 1 | yes (20³ = 8000 = 186·43 + 2) |
| 720763 | 43 | 632375 | no |

*Quartic witnesses* (`p ≡ q mod 720720`, both `≡ 1 mod 4`):

| p | 2^((p-1)/4) mod p | 2 a fourth power mod p? |
|---|---|---|
| 137 | 136 | no |
| 720857 | 1 | yes (96769⁴ ≡ 2) |

*Leakage saturation* (bases `2,3,5,7,11`; the 68 primes `p ∈ [1000,2000]` with
`p ≡ 1 mod 3`):

| fingerprint | distinct values | capacity |
|---|---|---|
| full quadratic symbols `a^((p-1)/2) mod p` | 68 / 68 | — (values live in `ZMod p`, i.e. already encode `p`) |
| full cubic symbols `a^((p-1)/3) mod p` | 68 / 68 | — (same artefact) |
| quadratic residuacity **bits** | 31 / 68 | `2⁵ = 32` |
| cubic residuacity **bits** | 23 / 68 | `2⁵ = 32` |

The "68/68 distinct" of the experiment is the circularity in numerical form: the
symbol's *value* lives in `ZMod p` and therefore carries `p` itself.  The
`p`-independent read-out — the residuacity bit — saturates at `2^K` for cubic
exactly as for quadratic, which is `PowerResidue.card_le_two_pow_of_injOn`.
-/


open PowerResidue

set_option exponentiation.threshold 1000000
set_option maxRecDepth 40000

/-! ## 1. The quadratic channel *is* a dial -/




/-! ## 2. Escape witnesses: explicit primes with equal residues and opposite
cubic (resp. quartic) bits -/






/-! ## 3. The cubic channel escapes every dial of conductor dividing `720720` -/

theorem PowerResidueEscape.witness_congr_p{M : ℕ} (hM : M ∣ 720720) : (137 : ℕ) % M = 720857 % M := by sorry
