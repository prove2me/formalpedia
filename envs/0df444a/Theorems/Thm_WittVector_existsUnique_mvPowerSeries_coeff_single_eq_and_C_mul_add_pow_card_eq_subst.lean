-- Prove2me | Theorems.Thm_WittVector_existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
-- name    : WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.759339+00:00
-- url     : https://prove2.me/theorems/b7ca4d4c-8abe-5798-8920-b121660de75e
-- title:
--   Lubin–Tate lemma for f(T)=pT+T^q over W(k)
-- statement:
--   Let $p$ be a prime, let $k$ be a finite field of characteristic $p$, write $q = \#k$ for its cardinality and $W(p,k)$ for the ring of $p$-typical Witt vectors of $k$. Let $\tau$ be a finite type and let $c : \tau \to W(p,k)$ be an arbitrary family of Witt vectors indexed by $\tau$. The assertion is that there is exactly one multivariate formal power series $\varphi$ in the variables $X_s$ ($s \in \tau$) with coefficients in $W(p,k)$ satisfying the following three conditions: its constant coefficient vanishes; for every $s \in \tau$ the coefficient of the monomial $X_s$ (the monomial with exponent vector `Finsupp.single s 1`) equals $c_s$; and the functional equation
--   $$p\,\varphi + \varphi^{q} \;=\; \varphi\bigl((p X_s + X_s^{q})_{s \in \tau}\bigr)$$
--   holds, where the right-hand side is the substitution into $\varphi$ of the series $p X_s + X_s^{q}$ for the variable $X_s$, and $p$ is understood as the image of the natural number $p$ in $W(p,k)$. Uniqueness is asserted among all power series, no further normalisation being imposed beyond the prescribed constant and linear coefficients.
--
--   This is the basic existence-and-uniqueness lemma of Lubin–Tate theory, here in the unramified case: $f(T) = pT + T^{q}$ is a Lubin–Tate series for the uniformiser $p$ of $W(k)$, and the statement produces, for each prescribed family of linear coefficients, the unique power series with zero constant term commuting with $f$; taking $\tau$ of size two or one yields the formal group law $F_f$ and its endomorphisms $[a]_f$, all of whose identities follow from the uniqueness clause. In this development it is used in the construction of special formal $\mathcal{O}_D$-modules in the Čerednik–Drinfel'd setting, namely by [`CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP`](thm.html#CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP) and by [`CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent`](thm.html#CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
    (τ : Type v) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ := by sorry
