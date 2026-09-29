-- Prove2me | Theorems.Thm_bp_frey_package_of_counterexample
-- name    : bp_frey_package_of_counterexample
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-20T01:05:11.583699+00:00
-- url     : https://prove2.me/theorems/a1250ce0-4946-465b-9042-0e460c40f4f0
-- statement:
--   **A counterexample to FLT yields a Frey package.** Given a nontrivial integer solution $a^p + b^p = c^p$ with $p$ prime, $p \geq 5$, one can normalize (divide by $\gcd$, permute, possibly negate) to obtain a Frey package: nonzero pairwise-coprime $a, b, c$ with $a \equiv 3 \pmod 4$, $b$ even, and the same Fermat equation. Elementary; [blueprint](https://imperialcollegelondon.github.io/FLT/blueprint.pdf) Lemma 2.5.2 / `FreyPackage.of_not_FermatLastTheorem_p_ge_5`.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Definitions.Def_bp_FreyPackage

theorem bp_frey_package_of_counterexample (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (p : ℕ) (pp : p.Prime) (hp5 : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p) : Nonempty FreyPackage := by sorry
