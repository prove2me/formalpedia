-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power
-- name    : ZetaNine.HarmonicStability.harmonic_den_dvd_lcm_power
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:34:46.711968+00:00
-- url     : https://prove2.me/theorems/f7ecff96-0cec-4e14-949e-054bfeedde67
-- title:
--   Actual harmonic denominators divide the finite lcm power
-- statement:
--   Let $s,N$ be any natural numbers, $H_N^{(s)}=\sum_{j=1}^{N}j^{-s}$, and $L_N=\operatorname{lcm}(1,\ldots,N)$, with $L_0=1$. Then
--
--   $$\operatorname{den}(H_N^{(s)})\mid L_N^s.$$
--
--   The result concerns the reduced denominator of the actual harmonic sum. It includes $s=0$ and $N=0$ and supplies the finite clearing bound used in the arithmetic argument. It makes no lower-bound or asymptotic prime-distribution assertion.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, section 2 clearing bound and section 3 Lemma 2 / Corollary 3.

import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open scoped BigOperators
open Filter
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_den_dvd_lcm_power (s N : ℕ) :
    (harmonicPower s N).den ∣ Nat.lcmUpto N ^ s := by sorry
