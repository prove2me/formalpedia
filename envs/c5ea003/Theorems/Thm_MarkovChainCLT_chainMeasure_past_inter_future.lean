-- Prove2me | Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future
-- name    : MarkovChainCLT.chainMeasure_past_inter_future
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T21:09:17.716991+00:00
-- url     : https://prove2.me/theorems/9a90d727-4bba-4989-96b9-0a4781f7302d
-- title:
--   Past $\cap$ future probability, disintegrated over the past
-- statement:
--   Let $P$ be a Markov kernel, $\lambda$ an initial distribution, and $\mathbb{P}_\lambda$ the resulting law on path space. Fix $k, n$ and measurable sets $A_0 \subseteq \prod_{i \le k}\mathsf{X}$ and $B_0 \subseteq \mathsf{X}^{\mathbb{N}}$. Then
--
--   $$\mathbb{P}_\lambda\Bigl(\mathrm{fr}_k^{-1}(A_0) \cap \bigl(\sigma^{k+n}\bigr)^{-1}(B_0)\Bigr) \;=\; \int_{A_0} \Bigl(\int_{\mathsf{X}} \mathbb{P}_y(B_0)\, P^{n}(u_k,\mathrm{d}y)\Bigr) \,\mathrm{d}\bigl[(\mathrm{fr}_k)_*\mathbb{P}_\lambda\bigr](u).$$
--
--   **What it is.** This is the joint law of a *past* event and a *future* event, disintegrated over the past. By the identification of the two $\sigma$-algebras of the coordinate process, every event in $\sigma(X_0,\dots,X_k)$ has the form $\mathrm{fr}_k^{-1}(A_0)$ and every event in $\sigma(X_{k+n},X_{k+n+1},\dots)$ has the form $(\sigma^{k+n})^{-1}(B_0)$, so the left-hand side is the completely general "past $\cap$ future" probability appearing in the definition of the mixing coefficients $\alpha(n)$, $\rho(n)$, $\phi(n)$.
--
--   **Why the right-hand side is the useful form.** It exhibits the joint probability as an average, over the past, of the *conditional* probability of the future — and that conditional probability is written explicitly as $\int \mathbb{P}_y(B_0)\,P^n(u_k,\mathrm{d}y)$, a quantity depending on the past only through the single state $u_k$. Comparing it with the stationary value $\int \mathbb{P}_y(B_0)\,\pi(\mathrm{d}y)$ and applying the total-variation bound for $[0,1]$-valued integrands converts a rate $\|P^n(x,\cdot)-\pi\| \le C$ directly into $\phi(n) \le C$, uniformly in the split point $k$. Everything after this point is arithmetic of averages: no measure-theoretic or Markov input remains.
--
--   **Proof.** Disintegrate $\mathbb{P}_\lambda$ over its first $k+1$ coordinates, writing it as $\mathrm{traj}_k$ composed with the marginal $(\mathrm{fr}_k)_*\mathbb{P}_\lambda$, and expand the resulting bind. It then suffices to evaluate $\mathrm{traj}_k(u)$ on the intersection, for each $u$.
--
--   Two facts do this. First, $\mathrm{traj}_k(u)$ reproduces its own initial segment: pushing it forward along $\mathrm{fr}_k$ gives $\mathrm{partialTraj}(k,k) = \mathrm{id}$, i.e. the Dirac mass at $u$. Hence the past event has $\mathrm{traj}_k(u)$-measure $\mathbf{1}_{A_0}(u)$ — it is *deterministic* given the conditioning, which is why it becomes an indicator and the integral restricts to $A_0$. When $u \in A_0$ its complement is null, so the intersection has the same measure as the future event alone; when $u \notin A_0$ the intersection is null.
--
--   Second, on the future event, the conditional restart theorem gives $(\sigma^{k+n})_*[\mathrm{traj}_k(u)] = \int \mathbb{P}_y\,P^n(u_k,\mathrm{d}y)$, which is exactly the inner integrand.
-- source:
--   C. J. Geyer, "Practical Markov Chain Monte Carlo", Statistical Science 7 (1992) 473-483, Section 3; S. P. Meyn and R. L. Tweedie, Markov Chains and Stochastic Stability, 2nd ed., Cambridge 2009, Ch. 16; R. C. Bradley, "Basic Properties of Strong Mixing Conditions. A Survey and Some Open Questions", Probability Surveys 2 (2005) 107-144; G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, Section 3.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

theorem MarkovChainCLT.chainMeasure_past_inter_future {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P]
    (lam : Measure X) [IsProbabilityMeasure lam] (k n : ℕ)
    (A₀ : Set (Π _i : Finset.Iic k, X)) (hA₀ : MeasurableSet A₀)
    (B₀ : Set (ℕ → X)) (hB₀ : MeasurableSet B₀) :
    (chainMeasure P lam) ((frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀)
        ∩ ((fun ω : ℕ → X => fun l => ω (k + n + l)) ⁻¹' B₀))
      = ∫⁻ u in A₀, ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀
          ∂((chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k)) := by sorry
