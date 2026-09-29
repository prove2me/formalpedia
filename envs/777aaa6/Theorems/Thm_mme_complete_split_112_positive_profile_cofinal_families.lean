-- Prove2me | Theorems.Thm_mme_complete_split_112_positive_profile_cofinal_families
-- name    : mme_complete_split_112_positive_profile_cofinal_families
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:04:39.070232+00:00
-- url     : https://prove2.me/theorems/854551bb-15fa-45ad-8548-77e77bbe2cf9
-- title:
--   Compatible induced families for every positive112 profile in the established hashing range
-- statement:
--   Let $l,g$ be nonnegative integers with $l>0$ and $341l<100g$. Put $D=l+g$. There exists a fixed $C\ge0$ such that, for every sufficiently large natural $m$, the compatible lengths $N=Dm$, $L=lm$, $G=gm$ admit an actual induced family with $A>0$ outer stars and $H>0$ components per star. Writing $Z=\binom{2N}{L}\binom{2N-L}{L}$, the same family satisfies
--
--   $$H\le4^N,\qquad Z e^{-C\sqrt{N+1}}\le A,\qquad \binom{2N}{N}e^{-2C\sqrt{N+1}}\le4AH.$$
--
--   This is the generic compatible-length construction for $p=l/(2D)$ in the range $0<p<50/441$. It preserves separate outer and joint directional capacities and constructs the finite family, rather than assuming extraction or asymptotic rates. The zero-parameter case requires a separate construction. It does not certify a complete numerical witness or a tensor-value bound.
-- source:
--   Generic compatible-length specialization of the already Proved q-independent uniform-star theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss, IDff1bc517-79c4-4b19-80e0-7c8195bc94c4, and exact joint count identity mme_primary_hash_uniform_stars_joint_directional_capacity, IDcc4487e0-01c9-4d2c-b972-d85620066096. Finite112 construction from Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Section6.3 printed pp58–59. Its use as a complete-profile consumer follows Alman et al., https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 printed pp14–15, pinned release TermInfoLv2.m lines134–146. This is a derived cofinal adapter preserving the original strict balance hypothesis, not a claim about all normalized released parameters.

import Definitions.Def_mme_CW_q6_primary_hash_family
import Mathlib.Analysis.SpecialFunctions.Exp

open MME Filter Topology

set_option autoImplicit false

theorem mme_complete_split_112_positive_profile_cofinal_families (l g : ℕ) (hl : 0 < l) (hbalance : 341 * l < 100 * g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N : ℕ := (l + g) * m
        let L : ℕ := l * m
        let G : ℕ := g * m
        let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by sorry
