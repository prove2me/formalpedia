-- Prove2me | Theorems.Thm_mme_dwz_common_state_CW_extraction_nonhole_index_mass
-- name    : mme_dwz_common_state_CW_extraction_nonhole_index_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:39:59.215983+00:00
-- url     : https://prove2.me/theorems/4ff17ca7-f08f-42cd-bfc8-d83c0b3d59e4
-- title:
--   A common hash state for actual CW extraction and nonhole index mass
-- statement:
--   Let $K$ be a field, $q,\ell,N,H,p,R\in\mathbb N$, and $p\ne0$ be odd. Put
--   $$
--   r=2^{\max\{\ell-1,0\}},\qquad L=2r,\qquad
--   T=\mathrm{CW}_q^{\otimes Nr},\qquad
--   \Omega=(\mathbb Z/p\mathbb Z)^{H+2}\times\mathbb Z/p\mathbb Z.
--   $$
--   Write $[n]=\{0,\ldots,n-1\}$, with $[0]=\varnothing$. Fix a positional bijection $[H+1]\simeq[N]$, component labels $c_a:[N]\to C$, and grade functions $g_i:C\to\mathbb N$ with $\sum_{i=0}^2g_i(c)=L$. Write $A_a(i,t)=g_i(c_a(t))$. Let $\mathcal T\subseteq\mathcal A\subseteq[R]$ be target and ambient owner sets. Targets have fixed modewise grade marginals; every address with these marginals and per-position grade sum $L$ is represented in $\mathcal A$.
--
--   For a three-term-progression-free $S\subseteq[\,\lfloor p/2\rfloor\,]$, let $E_a\subseteq\Omega$ be exactly the DWZ asymmetric-affine retention event: the three hashes of $A_a$ coincide at a residue represented in $S$.
--
--   Let $C,W$ have decidable equality. Fix a tag $\theta:\{0,1,2\}^r\to W$, an involution $\iota$, and nonnegative integer count tables $\mu_i(c,w)$, with
--   $$
--   \theta(2-v)=\iota(\theta(v)),\quad
--   g_0(c)=0\Rightarrow\mu_2(c,w)=\mu_1(c,\iota(w)),\quad
--   g_1(c)=0\Rightarrow\mu_2(c,w)=\mu_0(c,\iota(w)).
--   $$
--   Reflection is coordinatewise. A fine word assigns an atomic-grade word to each position. Write $G_i(a,f)$ for its per-position grades matching $A_a(i,-)$, and $P_i(a,f)$ for its component/tag counts being exactly $\mu_i$. Define $\operatorname{Comp}(f,b)$ by $G_2(b,f)$ and the $P_2$ count equalities restricted to zero-X or zero-Y components.
--
--   Fix a finite index set $B$ and arbitrary maps $f_a:B\to(\{0,1,2\}^r)^{[N]}$, with $G_2(a,f_a(u))$ and $P_2(a,f_a(u))$ for every target $a$ and index $u$. Let
--   $$
--   \mathcal C(a,u)=\{b\in\mathcal T:b\ne a,\ \operatorname{Comp}(f_a(u),b)\}.
--   $$
--   Assume integers $\kappa,J,D,C_*\ge0$ satisfy $\kappa=pJ$, $4D\le p$, and $8C_*\le p$. For every target, assume $|E_a|=\kappa$, both ambient X/Y star sizes are at most $D$, and $|\mathcal C(a,u)|\le C_*$. Assume $|E_a\cap E_b|\le J$ for distinct ambient X/Y-sharing competitors and for every $b\in\mathcal C(a,u)$.
--
--   Let $\mathcal S_\omega$ be the retained targets isolated against every retained ambient X/Y-sharing owner, and set
--   $$
--   \mathcal N_\omega(a)=\{u\in B:\forall b\in\mathcal S_\omega,\
--   \operatorname{Comp}(f_a(u),b)\Rightarrow b=a\}.
--   $$
--   Let $U_{\omega,a}$ be the canonical-coordinate projection of $T$ imposing $G_i$ in every mode, the full $P_2$ table in Z, and compatibility with no other selected owner in Z. No boundary X/Y profile filters remain.
--
--   Then there exist one state $\omega$, an integer $k$, and a bijection $e:[k]\simeq\mathcal S_\omega$ such that
--   $$
--   \bigoplus_{j<k}U_{\omega,e(j)}\preceq T,\qquad
--   8|\Omega|\sum_{a\in\mathcal S_\omega}|\mathcal N_\omega(a)|
--   \ge3|\mathcal T||B|\kappa.
--   $$
--   Moreover, $u\in\mathcal N_\omega(e(j))$ is equivalent to the full useful, unique-owner Z mask of this tensor evaluated at $f_{e(j)}(u)$, with owner uniqueness transported through $e$.
--
--   This counts indices, not distinct fine words or nonzero blocks: the maps $f_a$ may repeat words, and words may have empty canonical fibers (including when $q=0$). Actual block mass requires per-owner bijections and availability proofs. No positive nonzero-copy count, standard-product identification, or hole-repair conclusion is asserted.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS1 and https://arxiv.org/html/2210.10173v5#S6.SS2, Sections 6.1–6.2, especially Claim 6.2, Definition 6.3, and Claim 6.8 / equation (24). Finite common-state assembly lemma extracted from these arguments; not a separately numbered theorem or the full asymptotic result.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Definitions.Def_mme_dwz_selected_owner_nonhole_data
import Definitions.Def_mme_tensor_rank
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
open MME.DWZSimultaneous MME.DWZOwnerMass
universe u v w
set_option autoImplicit false

theorem mme_dwz_common_state_CW_extraction_nonhole_index_mass
    {K : Type u} [Field K] {C : Type v} {W : Type w} {Block : Type*}
    [DecidableEq C] [DecidableEq W] [Fintype Block] [DecidableEq Block]
    (q ell N H p R : ℕ) [NeZero p]
    (component : Fin R → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (marginal : Fin 3 → ℕ → ℕ)
    (targets ambient : Finset (Fin R)) (hsub : targets ⊆ ambient)
    (hmarginal : ∀ a ∈ targets, SameMarginal marginal (owner component shape a))
    (hcomplete : ∀ a : CoarseAddress N,
      Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      ∃ b ∈ ambient, owner component shape b = a)
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (events : Fin R → Finset ((Fin (H + 2) → ZMod p) × ZMod p))
    (hevents : ∀ a state, state ∈ events a ↔
      Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape a))
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (embed : Fin R → Block → FineWord ell N)
    (huseful : ∀ a ∈ targets, ∀ z,
      Graded component shape a 2 (embed a z) ∧ Profile component tag mu a 2 (embed a z))
    (K0 J d c : ℕ) (hK : K0 = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K0)
    (hx : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 0 = owner component shape a 0)).card ≤ d)
    (hy : ∀ a ∈ targets,
      (ambient.filter (fun b ↦ owner component shape b 1 = owner component shape a 1)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z,
      (competitors targets embed (fun f b ↦ ZCompatible component shape tag mu b f) a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (owner component shape b 0 = owner component shape a 0 ∨
        owner component shape b 1 = owner component shape a 1) →
      (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z,
      ∀ b ∈ competitors targets embed (fun f b ↦ ZCompatible component shape tag mu b f) a z,
      (events a ∩ events b).card ≤ J) :
    ∃ state : (Fin (H + 2) → ZMod p) × ZMod p, ∃ k : ℕ,
      ∃ enumerate : Fin k ≃ ↥(selected targets ambient events
        (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j : Fin k ↦
          (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
            (fun i w ↦
              Graded (fun j t ↦ component (enumerate j).val t)
                shape j i (label q ell N w) ∧
              (i = 2 → Profile (fun j t ↦ component (enumerate j).val t)
                tag mu j 2 (label q ell N w)) ∧
              (i = 2 → ∀ j',
                ZCompatible (fun j t ↦ component (enumerate j).val t)
                  shape tag mu j' (label q ell N w) → j' = j))))
        (source K q ell N) ∧
      (∀ j : Fin k, ∀ z : Block,
        z ∈ nonholes
          (selected targets ambient events
            (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state)
          embed (fun f b ↦ ZCompatible component shape tag mu b f) (enumerate j).val ↔
        Graded (fun j t ↦ component (enumerate j).val t)
          shape j 2 (embed (enumerate j).val z) ∧
        Profile (fun j t ↦ component (enumerate j).val t)
          tag mu j 2 (embed (enumerate j).val z) ∧
        ∀ j', ZCompatible (fun j t ↦ component (enumerate j).val t)
          shape tag mu j' (embed (enumerate j).val z) → j' = j) ∧
      3 * (targets.card * Fintype.card Block * K0) ≤
        8 * (Fintype.card ((Fin (H + 2) → ZMod p) × ZMod p) *
          ∑ a ∈ selected targets ambient events
            (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state,
            (nonholes
              (selected targets ambient events
                (fun a ↦ owner component shape a 0) (fun a ↦ owner component shape a 1) state)
              embed (fun f b ↦ ZCompatible component shape tag mu b f) a).card) := by sorry
