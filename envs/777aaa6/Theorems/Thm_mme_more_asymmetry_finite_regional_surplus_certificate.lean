-- Prove2me | Theorems.Thm_mme_more_asymmetry_finite_regional_surplus_certificate
-- name    : mme_more_asymmetry_finite_regional_surplus_certificate
-- status  : Open
-- author  : @raresbuhai
-- created : 2026-09-13T15:19:44.014181+00:00
-- url     : https://prove2.me/theorems/6f3dbd5d-dc21-405c-ab82-751be1d41094
-- title:
--   Construct a finite regional CW certificate with strict More Asymmetry surplus
-- statement:
--   Construct finite CW5 position and level data, profile predicates, and a recursive regional recipe $D$ whose computed matrix volume is at least one and whose retained value strictly beats its entire source cost at $\tau=3952233/5000000$:
--
--   $$I(D)\,7^N < O(D)\,[a(D)b(D)c(D)]^\tau.$$
--
--   The recipe must supply actual finite hash selections and ownership, all three mode-hole bounds including parent-profile rejection, exact-type coverage, region partitions, level descents, and terminal complementary boundary profiles. All type-cover input copies and repair output losses are charged by the recipe definitions. It contains no assumed tensor restriction, degeneration, or isomorphism.
--
--   This is the substantive open existence and quantitative certificate problem. The separately proved recipe soundness and surplus conversion imply the campaign goal once this witness is constructed. A route from the paper must prove sufficiently efficient finite realizations and losses and certify strict numerical slack; the released floating-point optimizer output is not such a proof.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3, Theorem 6.4, Section 7 and Table 1. Finite certificate target inspired by the original q=5 fourth-power bound 2.371339, with conversion slack at 3*(3952233/5000000)=2.3713398. Existence of this concrete recipe is left open; this is not a claim to have formalized the paper quantitative realization theorem.

import Definitions.Def_mme_recursive_regional_CW_data
import Definitions.Def_mme_omega
open MME MME.TensorObj MME.ProfiledCW
universe u
set_option autoImplicit false

theorem mme_more_asymmetry_finite_regional_surplus_certificate :
    ∃ (N ell : ℕ) (P : Predicate N) (D : RegionalPlan N ell P),
      1 ≤ D.a * D.b * D.c ∧
      ((D.inputs * 7 ^ N : ℕ) : ℝ) <
        (D.outputs : ℝ) * (((D.a * D.b * D.c : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by sorry
