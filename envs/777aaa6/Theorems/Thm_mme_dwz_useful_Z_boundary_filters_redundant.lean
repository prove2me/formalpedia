-- Prove2me | Theorems.Thm_mme_dwz_useful_Z_boundary_filters_redundant
-- name    : mme_dwz_useful_Z_boundary_filters_redundant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:19:13.215958+00:00
-- url     : https://prove2.me/theorems/56cb6396-0c88-4347-9dda-2b60779ba8c2
-- title:
--   Removing redundant boundary X/Y filters from useful CW projections
-- statement:
--   Let $K$ be a field, let $q,\ell,N,k$ be nonnegative integers, and put
--   $$
--   d=2^{\max\{\ell-1,0\}},\qquad T=\mathrm{CW}_q^{\otimes Nd}.
--   $$
--   Let $C,W$ be sets with decidable equality. For each owner $j<k$ and position $t<N$, fix a component label $c_j(t)\in C$, and assign each component three coarse grades $a_i(c)\in\mathbb N$. Fix a tag map $\theta:\{0,1,2\}^d\to W$, an involution $\iota$ of $W$, and nonnegative integer count tables $\mu_i(c,w)$. Assume
--   $$
--   \theta(2-v)=\iota(\theta(v)),
--   $$
--   where reflection is coordinatewise, and assume the boundary identities
--   $$
--   a_0(c)=0\Longrightarrow\mu_2(c,w)=\mu_1(c,\iota(w)),\qquad
--   a_1(c)=0\Longrightarrow\mu_2(c,w)=\mu_0(c,\iota(w)).
--   $$
--
--   Fix an owner $j$. Define $U_j$ by the following literal canonical-basis projection of $T$. In every mode the sum of the $d$ atomic grades at position $t$ must equal $a_i(c_j(t))$. In Z, additionally retain exactly those words having the prescribed tag counts $\mu_2(c,w)$ on every component and boundary-compatible with no owner other than $j$. Boundary compatibility with an owner means agreement with its coarse Z-address and agreement with the $\mu_2$ counts on every zero-X or zero-Y component.
--
--   Define $V_j$ by imposing the same conditions as $U_j$ and also the boundary X/Y filters: X tag counts equal $\mu_0(c,w)$ on zero-Y components, and Y tag counts equal $\mu_1(c,w)$ on zero-X components. Then
--   $$
--   U_j\preceq V_j.
--   $$
--
--   Thus the boundary X/Y coordinate filters can be removed by explicit linear maps while retaining the full useful Z count table and the same unique-owner Z predicate. The claim uses the actual CW tensor; it assumes neither a coefficient-support implication nor a tensor restriction. The count tables need not be normalized or realizable, and zero projected tensors are permitted. This is a coordinate-space padding result, not yet a regrouping into a product of component tensors or a hole-repair theorem.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS1, Section 6.1, Claim 6.2 and the description of the ideal tensor immediately following Additional Zeroing-Out Step 2. Finite coordinate-map normalization lemma extracted from that argument; not a separately numbered theorem in the paper.

import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Definitions.Def_mme_tensor_rank

open MME Module PiTensorProduct BigOperators
open MME.TensorObj MME.CompleteSplit MME.DWZStep1Support MME.DWZSimultaneous
universe u v w
set_option autoImplicit false

theorem mme_dwz_useful_Z_boundary_filters_redundant
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (j : Fin k) :
    TensorObj.Restrict
      ((source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
        (fun i w ↦
          Graded component shape j i (label q ell N w) ∧
          (i = 2 → Profile component tag mu j 2 (label q ell N w)) ∧
          (i = 2 → ∀ j', ZCompatible component shape tag mu j' (label q ell N w) → j' = j)))
      ((source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
        (fun i w ↦ Allowed component shape tag mu j i (label q ell N w))) := by sorry
