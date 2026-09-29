-- Prove2me | Theorems.Thm_mme_type2_threeAP_hash_retains_ambient_completion
-- name    : mme_type2_threeAP_hash_retains_ambient_completion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:05:34.990295+00:00
-- url     : https://prove2.me/theorems/576f0694-0cc8-4340-98c0-afeda1cf1008
-- title:
--   Three-AP-free type-2 hashing preserves ambient completions
-- statement:
--   Let the three vertex hashes of every supported tripartite mixture obey $H_0(x)+H_1(y)=2H_2(z)$ modulo $M$. Retain an edge when all three hashes equal one label from a three-term-progression-free set $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$. Then every ambient edge completing three retained vertices is retained as well. Indeed, the three labels form a modular arithmetic progression; the lower-half and three-AP-free hypotheses force them to coincide.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3, pp. 356-360; Salem--Spencer hash closure.

import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false

theorem mme_type2_threeAP_hash_retains_ambient_completion
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    (M : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (M / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (hash : ∀ i, Vertex i → ZMod M)
    (retained : Edge → Prop)
    (hretained : ∀ e, retained e ↔ ∃ s ∈ S, ∀ i : Fin 3, hash i (vertex i e) = (s : ZMod M))
    (hAP : ∀ x y z, supportedMix x y z → hash 0 (vertex 0 x) + hash 1 (vertex 1 y) = 2 * hash 2 (vertex 2 z))
    (ambient : Finset Edge)
    (x y z : Edge) (hx : retained x) (hy : retained y) (hz : retained z) (hsupp : supportedMix x y z)
    (hcomplete : ∃ e ∈ ambient, vertex 0 e = vertex 0 x ∧ vertex 1 e = vertex 1 y ∧ vertex 2 e = vertex 2 z) :
    ∃ e ∈ ambient, retained e ∧ vertex 0 e = vertex 0 x ∧ vertex 1 e = vertex 1 y ∧ vertex 2 e = vertex 2 z := by
  sorry
