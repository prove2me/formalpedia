-- Prove2me | Theorems.Thm_sensitivity_explicit_integer_amplification
-- name    : sensitivity_explicit_integer_amplification
-- status  : Proved
-- author  : @spongeboi
-- created : 2026-11-14T08:35:13.467479+00:00
-- url     : https://prove2.me/theorems/ec8d8f05-86e6-4399-9d02-d3bac8657b0c
-- title:
--   An explicit integer repetition bound absorbs sensitivity overhead
-- statement:
--   Let $C,R,G,p,q$ be natural numbers with $R>0$ and
--   $$R^p<G^q.$$
--   Define the explicit positive repetition count
--   $$M=C^pR^p+1.$$
--   Then
--   $$(CR^M)^p<(G^M)^q.$$
--
--   This gives a concrete amplification length for a fixed multiplicative sensitivity overhead $C$. In the profile-cycle setting, $R$ bounds sensitivity growth and $G$ bounds block-sensitivity growth. The inequality remains entirely in natural-number arithmetic. The bound is a sufficient bound, not a claim of optimality. It does not construct a profile-cycle certificate or establish a new separation exponent.
-- source:
--   Original explicit quantitative refinement of the constant-overhead step in the accepted profile-cycle reduction, Prove2Me submission de8328d7-41ea-4f05-b8d2-36de4c1eec70 for SensitivityCampaign.reach_215, https://prove2.me/theorems/d9f3f773-9b62-4684-8705-7695ad1882d7 . The new bound is M=C^p R^p+1. Proof uses the denominator-cleared Bernoulli inequality pow_add_mul_le_add_pow, Mathlib/Algebra/Order/Ring/Pow.lean, lines 83-89 at commit 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Ring/Pow.lean . The accepted source attributes its logarithmic growth argument to yousofy with Codex; this proof instead uses the elementary integer bound.

import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

theorem sensitivity_explicit_integer_amplification
    (C R G p q : ℕ) (hR : 0 < R) (hgap : R ^ p < G ^ q) :
    (C * R ^ (C ^ p * R ^ p + 1)) ^ p <
      (G ^ (C ^ p * R ^ p + 1)) ^ q := by sorry
