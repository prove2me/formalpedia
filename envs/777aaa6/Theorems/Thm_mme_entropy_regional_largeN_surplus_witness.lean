-- Prove2me | Theorems.Thm_mme_entropy_regional_largeN_surplus_witness
-- name    : mme_entropy_regional_largeN_surplus_witness
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-19T20:49:33.614683+00:00
-- url     : https://prove2.me/theorems/46c1315c-4168-458e-9757-2ea0f5406b80
-- title:
--   Large-N surplus recipe exists
-- statement:
--   There is a large-level entropy recipe witnessing surplus.
--
--   Let $N$, $\ell$, $P$, and $D$ range over levels, sizes, profile predicates, and finite entropy recipes in the More Asymmetry regional setting. Write $I(D)$ for charged inputs, $O(D)$ for guaranteed outputs, and $a(D),b(D),c(D)$ for matrix dimensions. Let $\tau=3952233/5000000$.
--
--   $$
--   I(D)\cdot 7^N < O(D)\cdot [a(D)b(D)c(D)]^{\tau}.
--   $$
--
--   Then there exist $N$, $\ell$, $P$, and $D$ with $N\ge 3$, $I(D)=1$, $a(D)b(D)c(D)\ge 1$, and the displayed strict surplus inequality. This is the remaining large-level existence obligation after small levels are ruled out: small-$N$ recipes never satisfy surplus, so any witness must come from $N\ge 3$ with genuine entropy copies and matching boundary data from the Section 6 numerical solution.
--
--   Formalization Note Lean states existence with explicit level, size, and predicate binders over EntropyRecipe.
-- source:
--   Uniform entropy-based integer regional construction for the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Large-N existence obligation after small-N delimitation; Section 6 numerical solution and Table 1.

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_entropy_regional_largeN_surplus_witness : exists (N ell : Nat) (P : MME.ProfiledCW.Predicate N) (D : EntropyRecipe N ell P), 3 <= N /\ D.inputs = 1 /\ 1 <= D.a * D.b * D.c /\ (((D.inputs * 7 ^ N : Nat) : Real) < (D.outputs : Real) * (((D.a * D.b * D.c : Nat) : Real) ^ ((3952233 : Real) / 5000000))) := by sorry
