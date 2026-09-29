-- Prove2me | Theorems.Thm_mme_type2_marginally_closed_profile_blocks_restrict
-- name    : mme_type2_marginally_closed_profile_blocks_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:14:59.628386+00:00
-- url     : https://prove2.me/theorems/47250a7c-94be-4939-9f00-5741efb68001
-- title:
--   Tensor realization of a marginally closed type-2 profile
-- statement:
--   Let a trilinear tensor $T$ carry a finite grading, and attach a length-$N$ grading address to every edge in an arbitrary finite three-partite edge alphabet. Let $S_0$ be a target profile inside an ambient same-marginal family $S$, and let $F\subseteq S_0$ be vertex-isolated. Assume supported mixed addresses admit ambient completion, $S_0$ is closed under completion from its three represented marginals, the three vertex maps are injective on $F$, and every coordinatewise nonzero mixed tensor block is supported. Then the direct sum of the retained address blocks is a restriction of the tensor power: $$\bigoplus_{e\in F} T_e \;\leq\; T^{\otimes N}.$$ The edge alphabet, the three mode alphabets, the profile, and the address map are all parameters. Thus this is the common tensor-realization endpoint for the type-2 extractions of $\varphi_{116},\varphi_{125},\varphi_{134}$, and $\varphi_{224}$; the nontrivial same-marginal correction for $\varphi_{233}$ remains an explicit separate hypothesis.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the type-2 construction in Section 3.2, printed pp. 356-360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; tensor zeroing realization of the retained induced family.

import Theorems.Thm_mme_induced_graded_address_blocks_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_type2_marginally_closed_profile_blocks_restrict
    {K : Type u} [Field K]
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge]
    {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t)
    (address : Edge → Fin 3 → Fin N → Fin t)
    (vertex : ∀ i, Edge → Vertex i)
    (supportedMix : Edge → Edge → Edge → Prop)
    (ambient target kept : Finset Edge)
    (hkept : kept ⊆ target)
    (hclosure : ∀ x ∈ target, ∀ y ∈ target, ∀ z ∈ target,
      supportedMix x y z →
        ∃ e ∈ ambient,
          vertex 0 e = vertex 0 x ∧
          vertex 1 e = vertex 1 y ∧
          vertex 2 e = vertex 2 z)
    (hprofile : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ target, vertex i e = vertex i f) →
        e ∈ target)
    (hisolated : ∀ e ∈ target,
      (∀ i : Fin 3, ∃ f ∈ kept, vertex i e = vertex i f) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1))
    (hblock : ∀ es : Fin 3 → kept,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ address (es i).1 i r) ≠ 0) →
      supportedMix (es 0).1 (es 1).1 (es 2).1) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock G (address (kept.equivFin.symm j).1)))
      (T.kronPow N) := by
  sorry
