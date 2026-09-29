-- Prove2me | Theorems.Thm_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
-- name    : groupCohomology.exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/89604047-9bff-5fcc-94ba-3de786770f67
-- title:
--   Dévissage to the trivial line for level 2-cocycles
-- statement:
--   Fix a prime $p$ and a group $G$, together with a homomorphism $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the levels), where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`. Let $T \colon \mathbb{N} \to$ subgroups of $G$ be antitone along divisibility, in the sense that $T M \le T N$ whenever $0 < N$ and $N \mid M$, and let $C$ be a set of subgroups of $G$ closed under $S \mapsto S \sqcap T N$ for $N > 0$. Assume the base case: for every $S \in C$ and every function $a \colon S \times S \to \mathbb{Z}/p$ lying in `levelCocycles₂` for the composite $r \circ S.\mathrm{subtype}$ and the trivial representation of $S$ on $\mathbb{Z}/p$, there is an $N > 0$ such that the restriction of $a$ along the inclusion $S \sqcap T N \le S$ lies in `levelCoboundaries₂` for the further composed homomorphism and the trivial representation of $S \sqcap T N$. Let now $S \in C$ and let $B$ be a representation of $S$ over $\mathbb{Z}/p$ that is finite-dimensional, such that: (i) every $b \in B$ is fixed by all $s \in S$ with $r(s)$ in the fixing subgroup of some finite extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ depending on $b$ (smoothness); and (ii) for every $s \in S$ there is $n$ with $B.\rho(s^{p^{n}}) = 1$. Then for every $b \colon S \times S \to B$ in `levelCocycles₂` $(r \circ S.\mathrm{subtype})\,B$ there exists $N > 0$ such that the restriction of $b$ to $(S \sqcap T N) \times (S \sqcap T N)$ along the inclusion lies in `levelCoboundaries₂` for the composed homomorphism and the restricted representation `Rep.res` of $B$ to $S \sqcap T N$.
--
--   This is the dévissage step reducing the statement "every level $2$-cocycle of a subgroup in the class $C$ becomes a level coboundary on some layer $S \sqcap T N$" from finite-dimensional smooth $\mathbb{F}_p$-representations with $p$-power-order action to the single case of the trivial one-dimensional representation, the induction being carried out by means of the long-exact-sequence criterion [`groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp`](thm.html#groupCohomology.comp_mem_levelCoboundaries2_iff_exists_levelCocycles2_sub_comp). It is used in the local analysis of continuous $H^2$, where $T N$ is the Galois group of the unramified layer cut out by $\mu_{q^{N}-1}$ and $C$ the open subgroups, via [`groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal`](thm.html#groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_restrict_mem_levelCoboundaries2_of_forall_pow_eq_one
    {p : ℕ} [Fact p.Prime] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup G) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (C : Set (Subgroup G)) (hC : ∀ S ∈ C, ∀ N : ℕ, 0 < N → S ⊓ T N ∈ C)
    (base : ∀ S ∈ C, ∀ a : S × S → Rep.trivial (ZMod p) S (ZMod p),
      a ∈ levelCocycles₂ (r.comp S.subtype) (Rep.trivial (ZMod p) S (ZMod p)) →
        ∃ (N : ℕ) (_ : 0 < N),
          (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
              a (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
            ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
                (Rep.trivial (ZMod p) ↥(S ⊓ T N) (ZMod p)))
    (S : Subgroup G) (hS : S ∈ C) (B : Rep.{0} (ZMod p) S) [FiniteDimensional (ZMod p) B]
    (hsm : ∀ b : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s b = b)
    (hP : ∀ s : S, ∃ n : ℕ, B.ρ (s ^ p ^ n) = 1)
    (b : S × S → B) (hb : b ∈ levelCocycles₂ (r.comp S.subtype) B) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : ↥(S ⊓ T N) × ↥(S ⊓ T N) =>
          b (Subgroup.inclusion inf_le_left g.1, Subgroup.inclusion inf_le_left g.2))
        ∈ levelCoboundaries₂ ((r.comp S.subtype).comp (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)))
            (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N ≤ S)) B) := by sorry
