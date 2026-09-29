-- Prove2me | Theorems.Thm_mme_entropy_regional_surplus_of_one_step
-- name    : mme_entropy_regional_surplus_of_one_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T09:08:25.948909+00:00
-- url     : https://prove2.me/theorems/ebec039f-e9fa-49db-970c-e57d85376492
-- title:
--   A finite entropy threshold and matching boundary imply regional surplus
-- statement:
--   Let S be an integer regional step on N elementary CW5 positions at a level l, and let B be a boundary endpoint at that same level whose predicate is exactly the output of S. Write E for the explicit entropy lower bound of S, r for its repair exponent, and V for the product of the three boundary dimensions. Suppose k is a positive integer, V is at least one, and, with tau = 3952233/5000000,
--
--   $$k 8^r \le E, \qquad 7^N < k V^{\tau}.$$
--
--   Then there is a finite entropy regional recipe D satisfying
--
--   $$1 \le a(D)b(D)c(D), \qquad I(D)7^N < O(D)(a(D)b(D)c(D))^{\tau}.$$
--
--   This is a conditional assembly criterion for the canonical regional surplus certificate. It retains the actual finite entropy and repair losses and requires a boundary matched to the very same step. It does not assert existence of S or B, nor that the displayed inequalities can be achieved.
-- source:
--   Direct consequence of the published definitions EntropyRecipe.descend and IntegerStep.entropyCopies in mme_entropy_regional_CW_recipe (0b48923b-4237-4298-a2fc-2fb10f2ab0f3) and mme_regional_entropy_copy_bound (3beca5f9-2804-45a6-a6fb-c06f208c8500), revision 777aaa61dcd2a1258d2b4962dbe983ede4d23b2e. Conditional assembly lemma for target mme_more_asymmetry_entropy_regional_surplus_certificate (32e9bef9-8029-4d9f-a4a5-7d4acaeb2d4c); not a claim of a numerical witness from the paper.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_surplus_of_one_step {N lower : Nat} {P : Predicate N} (S : IntegerStep lower N P) (B : BoundaryEnd lower N S.output) (copies : Nat) (hcopies : 0 < copies) (hthreshold : ((copies * 8 ^ S.repairExponent : Nat) : Real) <= S.entropyLower) (hdims : 1 <= B.a * B.b * B.c) (hsurplus : ((7 ^ N : Nat) : Real) < (copies : Real) * (((B.a * B.b * B.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) : exists (N ell : Nat) (P : Predicate N) (D : EntropyRecipe N ell P), And (1 <= D.a * D.b * D.c) (((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by sorry
