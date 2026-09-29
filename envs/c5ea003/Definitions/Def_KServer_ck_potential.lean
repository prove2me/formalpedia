-- Prove2me | Definitions.Def_KServer_ck_potential
-- name    : KServer_ck_potential
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T07:00:49.600177+00:00
-- url     : https://prove2.me/theorems/384b0dcc-bf01-494d-b346-c26019f670a3
-- title:
--   The Coester–Koutsoupias potential for three servers
-- statement:
--   The potential function with which Coester and Koutsoupias prove their $k$-server competitiveness results, instantiated for three servers.
--
--   For anchors $x_1, x_2, x_3$ in the base space $M$, the **anchored potential** is
--
--   $$\Phi_{x_1x_2x_3}(w) \;=\; w(x_1x_2x_3) \;+\; w(\bar x_1 x_2 x_3) \;+\; w(\bar x_2 \bar x_2 x_3) \;+\; w(\bar x_3 \bar x_3 \bar x_3),$$
--
--   a sum of $k+1 = 4$ work-function values in which the $i$-th term places $i$ servers at the antipode $\bar x_i$; the work function $w$ is that of the instance $(C_0, \sigma)$ evaluated in the antipodal extension $M \cup \bar M$, where every point has an antipode at distance $2\Delta$. The **potential** itself is
--
--   $$\Phi(w) \;=\; \min_{x_1, x_2, x_3 \in M} \Phi_{x_1x_2x_3}(w),$$
--
--   the minimum over anchor triples from the base space (`ckPot`, with `ckPot_le` and `exists_ckPot_eq` recording that the infimum over the finite anchor space is a lower bound and attained).
--
--   ## Role
--
--   The potential certifies $3$-competitiveness of the Work Function Algorithm through two properties. The **offset property** --- $\Phi(w) \le 4\,w(X) + c$ for every configuration $X$, with $c$ depending only on the space --- holds on any bounded space, each summand being within a bounded distance of any work-function value. The **update property** --- the potential increases by at least the extended cost at each request --- is where the geometry enters: it follows whenever the minimum above can be attained at a triple whose *last* anchor is the current request, since then the first three summands never decrease while the increase of the last, $w(\bar r^3)$, dominates the extended cost by Koutsoupias--Papadimitriou duality. Establishing that anchoring on trees is the content of Coester--Koutsoupias' Lemmas 24--26 and Theorem 23.
--
--   ## Formalization note
--
--   Anchors range over the **base space** $M$, not the extension: this matches the evader-view definition of the potential (a permutation of the points of $M$) and is the form the tree analysis needs, since the four-point condition holds only for original points. The extension enters through `antipodalExtension` on the sum type $M \oplus M$, originals embedded by `Sum.inl` and antipodes written `Sum.inr`; `Fintype M` with `Nonempty M` makes the minimum a genuine attained minimum.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential', eq. (antiPot): Φ_{x₁,…,x_k}(w) = Σ_{i=0}^k w(x̄_i^i x_{i+1}…x_k), Φ(w) = min Φ_{x₁,…,x_k}(w); instantiated for k = 3 with anchors from the base space (the evader-view equivalence, their Lemma preceding Corollary 20).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

variable (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)

/-- The **anchored Coester–Koutsoupias potential** for three servers: for anchors
`x₁ x₂ x₃` of the base space,

  `Φ_{x₁x₂x₃}(w) = w(x₁x₂x₃) + w(x̄₁x₂x₃) + w(x̄₂x̄₂x₃) + w(x̄₃x̄₃x̄₃)`,

where `w` is the work function of the instance `(C₀, σ)` evaluated in the antipodal
extension `M ⊕ M` and `x̄` denotes the antipode of `x`. -/
noncomputable def ckPotAt (C₀ : Config 3 M) (σ : List M) (x₁ x₂ x₃ : M) : ℝ :=
  @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inl x₁, Sum.inl x₂, Sum.inl x₃]
    + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₁, Sum.inl x₂, Sum.inl x₃]
    + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₂, Sum.inr x₂, Sum.inl x₃]
    + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) ![Sum.inr x₃, Sum.inr x₃, Sum.inr x₃]

/-- The **Coester–Koutsoupias potential**: the minimum of the anchored potential
over all triples of anchors from the base space. -/
noncomputable def ckPot [Fintype M] [Nonempty M] (C₀ : Config 3 M) (σ : List M) : ℝ :=
  ⨅ t : M × M × M, ckPotAt M Δ hΔ0 hΔ C₀ σ t.1 t.2.1 t.2.2

theorem ckPot_le [Fintype M] [Nonempty M] (C₀ : Config 3 M) (σ : List M) (x₁ x₂ x₃ : M) :
    ckPot M Δ hΔ0 hΔ C₀ σ ≤ ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃ :=
  ciInf_le (Finite.bddBelow_range _) (⟨x₁, x₂, x₃⟩ : M × M × M)

theorem exists_ckPot_eq [Fintype M] [Nonempty M] (C₀ : Config 3 M) (σ : List M) :
    ∃ x₁ x₂ x₃ : M, ckPot M Δ hΔ0 hΔ C₀ σ = ckPotAt M Δ hΔ0 hΔ C₀ σ x₁ x₂ x₃ := by
  obtain ⟨⟨x₁, x₂, x₃⟩, ht⟩ :=
    exists_eq_ciInf_of_finite (f := fun t : M × M × M => ckPotAt M Δ hΔ0 hΔ C₀ σ t.1 t.2.1 t.2.2)
  exact ⟨x₁, x₂, x₃, ht.symm⟩

end KServer


