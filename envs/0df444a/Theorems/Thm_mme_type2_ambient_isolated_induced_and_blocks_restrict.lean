-- Prove2me | Theorems.Thm_mme_type2_ambient_isolated_induced_and_blocks_restrict
-- name    : mme_type2_ambient_isolated_induced_and_blocks_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:27:22.064588+00:00
-- url     : https://prove2.me/theorems/bd1d74e3-2651-4e94-808e-5623121f10c0
-- title:
--   Ambient-isolated type-2 family is induced and tensor-realizable
-- statement:
--   Let $F$ be a finite retained target family of three-partite edges inside an ambient same-marginal family $S$. Give each edge a vertex in each of three arbitrary mode alphabets and a length-$N$ grading address in a trilinear tensor $T$. Assume every supported mixture of three target edges has a completion in $S$; every ambient edge whose three vertices are represented in $F$ already belongs to $F$; the three vertex maps are injective on $F$; and every coordinatewise nonzero mixed tensor block is supported. Then $F$ is an induced three-partite matching and its graded blocks are simultaneously realized: $$\operatorname{SuppMix}(x,y,z)\Longrightarrow x=y=z, \qquad \bigoplus_{e\in F}T_e\le T^{\otimes N}.$$ Ambient isolation makes the theorem valid even for a nontrivial same-marginal target fiber, so it is the common structural endpoint for all five type-2 Davie--Stothers constituent analyses, including $\varphi_{233}$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the type-2 construction in Section 3.2, printed pp. 356-360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; tensor zeroing realization of the retained induced family.

import Theorems.Thm_mme_induced_graded_address_blocks_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_type2_ambient_isolated_induced_and_blocks_restrict
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
    (hisolated : ∀ e ∈ ambient,
      (∀ i : Fin 3, ∃ f ∈ kept, vertex i e = vertex i f) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦ vertex i e.1))
    (hblock : ∀ es : Fin 3 → kept,
      (∀ r : Fin N,
        G.blockTensor (fun i ↦ address (es i).1 i r) ≠ 0) →
      supportedMix (es 0).1 (es 1).1 (es 2).1) :
    (∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z) ∧
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j : Fin kept.card ↦
        gradedAddressBlock G (address (kept.equivFin.symm j).1)))
      (T.kronPow N) := by
  sorry
