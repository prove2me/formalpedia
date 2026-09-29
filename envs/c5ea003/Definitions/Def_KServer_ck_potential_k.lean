-- Prove2me | Definitions.Def_KServer_ck_potential_k
-- name    : KServer_ck_potential_k
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-07T10:30:42.840028+00:00
-- url     : https://prove2.me/theorems/61957520-18db-4577-941f-29ce0405a338
-- title:
--   The Coester--Koutsoupias potential for $k$ servers
-- statement:
--   The **Coester–Koutsoupias potential** for $k$ servers, in the general-$k$ form of which `KServer.ckPot` is the $k = 3$ instance.
--
--   Let $M$ be a metric space, let $\Delta > 0$ bound all distances of $M$, and let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$ (`KServer.antipodalExtension`), in which every point $q$ has an antipode $\bar q$ with $d(y,q) + d(y,\bar q) = 2\Delta$ for all $y$. Fix an initial configuration $C_0$ of $k$ servers and a request sequence $\sigma$, both drawn from $M$, and let
--   $$\widehat w(X) \;=\; \widehat w\bigl(C_0;\sigma;X\bigr)$$
--   be the unordered work function of the instance, evaluated in $N$.
--
--   **Anchored potential.** For anchors $x_1,\dots,x_k \in M$,
--   $$\Phi_{x_1\dots x_k} \;=\; \widehat w(x_1 x_2 \cdots x_k) \;+\; \sum_{i=1}^{k} \widehat w\bigl(\bar x_i^{\,i}\, x_{i+1} \cdots x_k\bigr),$$
--   where $\bar x_i^{\,i}$ denotes $i$ servers coalesced on the antipode of $x_i$. The $k+1$ terms interpolate between the all-original configuration $x_1\cdots x_k$ and the fully coalesced antipodal configuration $\bar x_k^{\,k}$.
--
--   **Potential.** For finite $M$,
--   $$\Phi \;=\; \min_{x_1,\dots,x_k \in M} \Phi_{x_1\dots x_k},$$
--   the minimum of the anchored potential over all $k$-tuples of anchors of the base space.
--
--   This is the potential proposed by Coester and Koutsoupias as a unifying route to the $k$-server conjecture: the conjecture follows from the assertion that, at every request, the increase of $\Phi$ dominates the increase of the work function at the coalesced configuration on the antipode of that request, together with the bound $\Phi \le (k+1)\,\mathrm{OPT} + \Delta k(k+1)$.
--
--   **Formalization Note** `ckConfigK x i` is the anchor configuration indexed by `i : Fin k`, i.e. the $(i+1)$-st term above: coordinates $j \le i$ carry `Sum.inr (x i)` (the antipode of the anchor $x_{i+1}$ in 1-based notation) and coordinates $j > i$ carry `Sum.inl (x j)`. `ckPotAtK` is the anchored potential and `ckPotK` the minimum over anchors, taken as an `iInf` over `Fin k → M`, which is a genuine minimum because `M` is a `Fintype`. Specializing to `k = 3` recovers `KServer.ckPotAt` and `KServer.ckPot` verbatim.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential': the potential Phi_{x_1...x_k}(w) = sum_{i=0}^{k} w(bar x_i^i x_{i+1} ... x_k) on the antipodal extension, minimized over anchors; k=3 instance already on the platform as KServer_ck_potential.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

/-- The `i`-th **anchor configuration** of the Coester–Koutsoupias potential, for anchors
`x₁ … x_k` of the base space `M` and `i : Fin k`: the configuration of the antipodal
extension `M ⊕ M` whose first `i+1` servers all sit on the antipode of the anchor `xᵢ`,
and whose remaining servers sit on the anchors `x_{i+1}, …, x_k` themselves. -/
def ckConfigK {k : ℕ} {M : Type} (x : Fin k → M) (i : Fin k) : Config k (M ⊕ M) :=
  fun j => if (j : ℕ) ≤ (i : ℕ) then Sum.inr (x i) else Sum.inl (x j)

/-- The **anchored Coester–Koutsoupias potential** for `k` servers: for anchors
`x₁ … x_k` of the base space,

  `Φ_{x₁ … x_k}(w) = w(x₁ … x_k) + Σ_{i=1}^{k} w(x̄ᵢ^i x_{i+1} … x_k)`,

where `w` is the work function of the instance `(C₀, σ)` evaluated in the antipodal
extension `M ⊕ M` and `x̄` denotes the antipode of `x`. -/
noncomputable def ckPotAtK (k : ℕ) (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (σ : List M) (x : Fin k → M) : ℝ :=
  @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
      (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (fun j => Sum.inl (x j))
    + ∑ i : Fin k, @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) (ckConfigK x i)

/-- The **Coester–Koutsoupias potential** for `k` servers: the minimum of the anchored
potential over all `k`-tuples of anchors from the base space. -/
noncomputable def ckPotK (k : ℕ) (M : Type) [MetricSpace M] [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (σ : List M) : ℝ :=
  ⨅ x : Fin k → M, ckPotAtK k M Δ hΔ0 hΔ C₀ σ x

theorem ckPotK_le (k : ℕ) (M : Type) [MetricSpace M] [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (σ : List M) (x : Fin k → M) :
    ckPotK k M Δ hΔ0 hΔ C₀ σ ≤ ckPotAtK k M Δ hΔ0 hΔ C₀ σ x :=
  ciInf_le (Finite.bddBelow_range _) x

theorem exists_ckPotK_eq (k : ℕ) (M : Type) [MetricSpace M] [Fintype M] [Nonempty M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M) (σ : List M) :
    ∃ x : Fin k → M, ckPotK k M Δ hΔ0 hΔ C₀ σ = ckPotAtK k M Δ hΔ0 hΔ C₀ σ x := by
  obtain ⟨x, hx⟩ :=
    exists_eq_ciInf_of_finite (f := fun x : Fin k → M => ckPotAtK k M Δ hΔ0 hΔ C₀ σ x)
  exact ⟨x, hx.symm⟩

end KServer


