-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
-- name    : groupCohomology.exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/944c4faa-9725-5506-be49-a65374275665
-- title:
--   A uniform level killing all continuous H² classes
-- statement:
--   Fix a prime $p$, a group $\Gamma$, and a homomorphism $r : \Gamma \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the datum with respect to which the level-wise cocycle and coboundary submodules `levelCocycles₂` and `levelCoboundaries₂` are formed). Let $T : \mathbb{N} \to$ subgroups of $\Gamma$ satisfy $T_M \le T_N$ whenever $0 < N$ and $N \mid M$, let $S \le \Gamma$, let $B$ be a representation of $S$ over $\mathbb{Z}/p$, and let $N_0 > 0$. Assume two things about $S \sqcap T_{N_0}$, equipped with the composite of $r$ with its inclusion into $\Gamma$ and with $B$ restricted along the inclusion $S \sqcap T_{N_0} \le S$: first, that $\mathrm{continuousH2}$ of this datum — the quotient of the module of level $2$-cocycles by the part of `levelCoboundaries₂` lying inside it — is finite-dimensional over $\mathbb{Z}/p$; second, that every $z : (S \sqcap T_{N_0})^2 \to B$ lying in `levelCocycles₂` has some $N > 0$ for which the function obtained by restricting $z$ to the preimage of $T_N$ in $S \sqcap T_{N_0}$ lies in `levelCoboundaries₂` for the correspondingly composed homomorphism and restricted representation. The conclusion produces one $N$, together with the inclusion $hle$ of the preimage of $T_N$ in $S$ into the preimage of $T_{N_0}$ in $S$, such that $N > 0$, $N_0 \mid N$, and every $b$ on the square of the preimage of $T_{N_0}$ in $S$ which lies in `levelCocycles₂` has its restriction along $hle$, on the square of the preimage of $T_N$ in $S$, lying in `levelCoboundaries₂`.
--
--   This is the uniformity step that converts per-cocycle vanishing of level $2$-cocycles deeper in a divisibility-ordered tower of subgroups into a single level at which all classes die, the input being finite-dimensionality of the associated continuous $H^2$. It is stated for an abstract group with a map to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ so that the local application, [`groupCohomology.exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal`](thm.html#groupCohomology.exists_forall_restrict_comap_rootsOfUnity_mem_levelCoboundaries2_of_primeLocal), is a specialisation to open subgroups of a local Galois group and its tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.exists_forall_restrict_comap_mem_levelCoboundaries2_of_finiteDimensional
    {p : ℕ} [Fact p.Prime] {Γ : Type} [Group Γ]
    (r : Γ →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (T : ℕ → Subgroup Γ) (hT : ∀ N M : ℕ, 0 < N → N ∣ M → T M ≤ T N)
    (S : Subgroup Γ) (B : Rep.{0} (ZMod p) S) (N₀ : ℕ) (hN₀ : 0 < N₀)
    (hfin : FiniteDimensional (ZMod p)
      (continuousH2 (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B)))
    (hvanish : ∀ z : ↥(S ⊓ T N₀) × ↥(S ⊓ T N₀) → B,
      z ∈ levelCocycles₂ (r.comp (S ⊓ T N₀).subtype) (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B) →
      ∃ (N : ℕ) (_ : 0 < N),
        (fun g : ↥((T N).comap (S ⊓ T N₀).subtype) × ↥((T N).comap (S ⊓ T N₀).subtype) =>
            z (((T N).comap (S ⊓ T N₀).subtype).subtype g.1, ((T N).comap (S ⊓ T N₀).subtype).subtype g.2))
          ∈ levelCoboundaries₂ ((r.comp (S ⊓ T N₀).subtype).comp ((T N).comap (S ⊓ T N₀).subtype).subtype)
              (Rep.res ((T N).comap (S ⊓ T N₀).subtype).subtype (Rep.res (Subgroup.inclusion (inf_le_left : S ⊓ T N₀ ≤ S)) B))) :
    ∃ (N : ℕ) (hle : (T N).comap S.subtype ≤ (T N₀).comap S.subtype), 0 < N ∧ N₀ ∣ N ∧
      ∀ b : ↥((T N₀).comap S.subtype) × ↥((T N₀).comap S.subtype) → B,
        b ∈ levelCocycles₂ ((r.comp S.subtype).comp ((T N₀).comap S.subtype).subtype) (Rep.res ((T N₀).comap S.subtype).subtype B) →
        (fun g : ↥((T N).comap S.subtype) × ↥((T N).comap S.subtype) => b (Subgroup.inclusion hle g.1, Subgroup.inclusion hle g.2))
          ∈ levelCoboundaries₂ ((r.comp S.subtype).comp ((T N).comap S.subtype).subtype) (Rep.res ((T N).comap S.subtype).subtype B) := by sorry
