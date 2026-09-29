-- Prove2me | Theorems.Thm_mme_type2_induced_of_marginally_closed_profile
-- name    : mme_type2_induced_of_marginally_closed_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:12:31.882784+00:00
-- url     : https://prove2.me/theorems/b4ff08e3-eb26-4328-8c95-75260f9ffbf3
-- title:
--   Type-2 profile closure yields an induced three-partite matching
-- statement:
--   Let $S_0$ be a finite target family of three-partite edges inside an ambient same-marginal family $S$, and let $F\subseteq S_0$ be a pruned family. Each edge $e$ has one vertex $v_i(e)$ in each of three arbitrary finite-mode alphabets. Assume: every supported mixture of three target edges has an ambient completion with the three selected vertices; $S_0$ is closed under such marginal completion inside $S$; $F$ is vertex-induced inside $S_0$; and every vertex map is injective on $F$. Then every supported mixed triple from $F$ is diagonal: $$\operatorname{SuppMix}(x,y,z)\Longrightarrow x=y=z.$$ This is the deterministic profile-closure step in the type-2 Salem--Spencer extraction. It separates the trivial-marginal-fiber input used for $\varphi_{116},\varphi_{125},\varphi_{134}$, and $\varphi_{224}$ from the nontrivial fiber correction required for $\varphi_{233}$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and the type-2 construction in Section 3.2, printed pp. 356-360, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Data.Finset.Card

set_option autoImplicit false

theorem mme_type2_induced_of_marginally_closed_profile
    {Edge : Type*} {Vertex : Fin 3 → Type*}
    [DecidableEq Edge]
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
      Function.Injective (fun e : kept ↦ vertex i e.1)) :
    ∀ x y z : kept,
      supportedMix x.1 y.1 z.1 → x = y ∧ y = z := by
  sorry
