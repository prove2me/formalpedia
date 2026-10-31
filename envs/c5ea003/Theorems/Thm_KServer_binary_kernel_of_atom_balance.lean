-- Prove2me | Theorems.Thm_KServer_binary_kernel_of_atom_balance
-- name    : KServer.binary_kernel_of_atom_balance
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T17:04:15.352685+00:00
-- url     : https://prove2.me/theorems/7c015df6-d8cf-4ba7-9ac6-9bda981603e1
-- title:
--   Finite binary transition law from conditional branch masses
-- statement:
--   Let $\Omega$ be a finite set with real weights $P_\omega$, and let $H:\Omega\to\mathbb N$ partition it into atoms. Let $B:\Omega\to\{\mathrm{false},\mathrm{true}\}$ choose a branch, and let $u,v,q:\Omega\to\mathbb R$ be constant on each atom. Suppose that for every atom $A$ and any $\omega_0\in A$,
--
--   $$\sum_{\omega\in A,\,B(\omega)=\mathrm{true}}P_\omega=q(\omega_0)\sum_{\omega\in A}P_\omega.$$
--
--   Let $Y(\omega)=u(\omega)$ when $B(\omega)=\mathrm{true}$ and $Y(\omega)=v(\omega)$ otherwise. Then every real test function $f$ satisfies
--
--   $$\sum_\omega P_\omega f(Y(\omega))=\sum_\omega P_\omega\left[q(\omega)f(u(\omega))+(1-q(\omega))f(v(\omega))\right].$$
--
--   For probability weights and $0\le q\le1$, the hypothesis specifies the branch probability conditional on the atom. The conclusion is the finite mixture law used to evaluate all moments of the next state.
--
--   **Formalization Note** The identity is algebraic and does not require positive weights, normalized total mass, or positive atom masses. In particular, it involves no division by atom mass.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (the probabilities p_L and p_R), and Section 4.2, equations (3)–(4), printed pp. 16–19. Elementary finite law of total expectation for the atomwise selection probabilities; the general algebraic formulation is proved here.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem KServer.binary_kernel_of_atom_balance {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (H : Ω → ℕ)
    (B : Ω → Bool) (u v q : Ω → ℝ)
    (hknown : ∀ ω ω', H ω = H ω' → u ω = u ω' ∧ v ω = v ω' ∧ q ω = q ω')
    (hbalance : ∀ ω₀,
      (∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀ ∧ B ω = true), P ω) =
        q ω₀ * (∑ ω ∈ Finset.univ.filter (fun ω => H ω = H ω₀), P ω)) :
    ∀ f : ℝ → ℝ,
      (∑ ω, P ω * f (if B ω then u ω else v ω)) =
        ∑ ω, P ω * (q ω * f (u ω) + (1 - q ω) * f (v ω)) := by sorry
