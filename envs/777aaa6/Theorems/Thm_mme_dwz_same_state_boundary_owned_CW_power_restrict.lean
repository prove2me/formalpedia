-- Prove2me | Theorems.Thm_mme_dwz_same_state_boundary_owned_CW_power_restrict
-- name    : mme_dwz_same_state_boundary_owned_CW_power_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T09:44:32.68818+00:00
-- url     : https://prove2.me/theorems/8976d663-4b66-438b-ae53-a9f8153765ea
-- title:
--   Same-state boundary-owned extraction from an actual CW power
-- statement:
--   Let $K$ be a field, and let $q,\ell,N,H,p,k$ be nonnegative integers. Put $d=2^{\max\{\ell-1,0\}}$ and $L=2d$, and fix a bijection from $\{0,\ldots,H\}$ to the $N$ positions. Let $C,W$ be sets with decidable equality. A component map $c_j(t)\in C$ and shape map $a:C\to\mathbb N^3$ determine selected coarse addresses
--   $$
--   A_j(i,t)=a_i(c_j(t)),\qquad j<k.
--   $$
--   Assume each shape has coordinate sum $L$, the addresses $A_j$ are distinct, and all selected addresses have prescribed marginal histograms $m_i(g)$.
--
--   Let $p$ be odd and let $S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\}$ be free of nontrivial three-term arithmetic progressions. Fix one state of the asymmetric hash. Assume every $A_j$ is retained by that state, and assume ambient X/Y isolation: any retained address with coordinate sum $L$ at every position and marginals $m_i(g)$ that shares its whole X-address or whole Y-address with $A_j$ equals $A_j$.
--
--   Let $\theta:\{0,1,2\}^d\to W$ be a tag map and let $\iota:W\to W$ be an involution such that
--   $$
--   \theta(2-v)=\iota(\theta(v)).
--   $$
--   Prescribe nonnegative integer histograms $\mu_i(c,w)$. On zero-X and zero-Y components, respectively, assume
--   $$
--   a_0(c)=0\Longrightarrow\mu_2(c,w)=\mu_1(c,\iota(w)),\qquad
--   a_1(c)=0\Longrightarrow\mu_2(c,w)=\mu_0(c,\iota(w)).
--   $$
--
--   For each owner $j$, define $T_j$ to be the coordinate projection of $T=\mathrm{CW}_q^{\otimes Nd}$ that keeps exactly the following canonical basis words:
--
--   1. In each mode, the sum of the $d$ atomic grades at position $t$ equals $a_i(c_j(t))$.
--   2. In X, the tag histogram on each zero-Y component is $\mu_0$; in Y, the tag histogram on each zero-X component is $\mu_1$.
--   3. In Z, the tag histogram on every component is $\mu_2$, and the word is boundary-compatible with no selected owner other than $j$. Boundary compatibility means the same coarse Z-address and the prescribed $\mu_2$ histograms on all zero-X or zero-Y components.
--
--   Then the actual simultaneous tensor restriction exists:
--   $$
--   \bigoplus_{j<k}T_j\ \preceq\ \mathrm{CW}_q^{\otimes Nd}.
--   $$
--   Here $\preceq$ denotes restriction by linear maps. No coefficient-isolation or tensor-realization hypothesis is assumed. The selected family may be empty, and the prescribed profiles may yield zero summands. This is a single-region finite extraction statement; it neither asserts a lower bound on the number of surviving blocks nor identifies the summands with normalized standard-form tensors. For $\ell=3$, the source is $\mathrm{CW}_q^{\otimes 4N}$.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS1, Section 6.1, Definition 6.1, Claim 6.2, Definition 6.3, and the direct-sum assertion immediately following Additional Zeroing-Out Step 2. This is an explicit finite, single-region CW-source realization lemma with arbitrary reflection-compatible tags, not the full asymptotic value theorem.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Definitions.Def_mme_tensor_rank
import Mathlib.Combinatorics.Additive.AP.Three.Defs

open BigOperators
open MME Module MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
open MME.DWZSimultaneous
universe u v w
set_option autoImplicit false

theorem mme_dwz_same_state_boundary_owned_CW_power_restrict
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N H p k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (hshape : ∀ c, shape c 0 + shape c 1 + shape c 2 = 2 * 2 ^ (ell - 1))
    (hinj : Function.Injective (owner component shape))
    (marginal : Fin 3 → ℕ → ℕ)
    (hmarginal : ∀ j, SameMarginal marginal (owner component shape j))
    (reindex : Fin (H + 1) ≃ Fin N)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (hpodd : Odd p)
    (state : (Fin (H + 2) → ZMod p) × ZMod p)
    (hretained : ∀ j, Retained (2 * 2 ^ (ell - 1)) reindex S state (owner component shape j))
    (hisolated : ∀ j a, Supported (2 * 2 ^ (ell - 1)) a → SameMarginal marginal a →
      Retained (2 * 2 ^ (ell - 1)) reindex S state a →
      (owner component shape j 0 = a 0 ∨ owner component shape j 1 = a 1) →
      a = owner component shape j)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin k ↦
        (source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
          (fun i w ↦ Allowed component shape tag mu j i (label q ell N w))))
      (source K q ell N) := by sorry
