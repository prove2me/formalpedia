-- Prove2me | Theorems.Thm_mme_dwz_selected_owner_nonhole_mass_and_disjointness
-- name    : mme_dwz_selected_owner_nonhole_mass_and_disjointness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T15:13:29.627287+00:00
-- url     : https://prove2.me/theorems/58695686-1543-46d0-86ed-4a89e23a5e16
-- title:
--   One common state with nonhole mass and disjoint block ownership
-- statement:
--   Let W be a nonempty finite state space, A⊆B finite families of addresses, and U a finite set of standard useful block indices. Each address a has two labels x(a),y(a) and a retaining event E_a⊆W. For each target a, a map e_a:U→Z supplies actual block labels. Let C(z,b) be compatibility and assume C(e_a(u),a) for every target a and u∈U.
--
--   Suppose |E_a|=K for all a∈A, where K=pJ. For each a∈A, assume its ambient X-star and Y-star have at most d elements, and each pair (a,u) has at most c compatible competing targets b≠a. Assume
--   $$
--   4d\le p,\qquad 8c\le p.
--   $$
--   The intersection |E_a∩E_b| must be at most J whenever b is a distinct ambient X/Y competitor of a, or a compatible competing target for (a,u).
--
--   At a state w, let S(w) be the retained targets isolated against every retained ambient X/Y competitor. Retain u in owner a exactly when C(e_a(u),b) implies b=a for every b∈S(w), and call this set N_w(a). Then there exists one state w such that x and y are each injective on S(w), retained block images have unique owners, and
--   $$
--   3|A||U|K\le 8|W|\sum_{a\in S(w)}|N_w(a)|.
--   $$
--   Precisely, if b∈S(w), u∈N_w(a), and e_a(u)=e_b(v), then b=a.
--
--   The sum counts standard block indices, not necessarily distinct actual labels. Converting it to actual block fractions additionally requires per-owner bijections. This theorem couples the quantitative common-state estimate with the ownership properties needed for a simultaneous tensor restriction; it does not assume or assert that the tensor normalization has already been constructed. Empty target or block families and K=0 are permitted.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2, Claim 6.8 and the subsequent Bounding the value argument; see also Section 6.1, Additional Zeroing-Out Steps 1 and 2. This is a finite event-counting bridge derived for the formalization, not a verbatim assertion of the paper.

import Definitions.Def_mme_dwz_selected_owner_nonhole_data
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open BigOperators MME.DWZOwnerMass
set_option autoImplicit false

theorem mme_dwz_selected_owner_nonhole_mass_and_disjointness
    {State Edge Block X Y Z : Type*}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [Fintype Edge] [DecidableEq Edge]
    [Fintype Block] [DecidableEq Block] [DecidableEq X] [DecidableEq Y]
    (targets ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (hsub : targets ⊆ ambient)
    (hself : ∀ a ∈ targets, ∀ z, compatible (embed a z) a)
    (K J p d c : ℕ) (hK : K = p * J)
    (hxyBudget : 4 * d ≤ p) (hzBudget : 8 * c ≤ p)
    (hsingle : ∀ a ∈ targets, (events a).card = K)
    (hx : ∀ a ∈ targets, (ambient.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ targets, (ambient.filter (fun b ↦ y b = y a)).card ≤ d)
    (hzCard : ∀ a ∈ targets, ∀ z,
      (competitors targets embed compatible a z).card ≤ c)
    (hxyPair : ∀ a ∈ targets, ∀ b ∈ ambient,
      b ≠ a → (x b = x a ∨ y b = y a) →
        (events a ∩ events b).card ≤ J)
    (hzPair : ∀ a ∈ targets, ∀ z, ∀ b ∈ competitors targets embed compatible a z,
      (events a ∩ events b).card ≤ J) :
    ∃ w : State,
      (Set.InjOn x (selected targets ambient events x y w : Set Edge) ∧
        Set.InjOn y (selected targets ambient events x y w : Set Edge)) ∧
      (∀ a b : Edge, b ∈ selected targets ambient events x y w → ∀ u v : Block,
        u ∈ nonholes (selected targets ambient events x y w) embed compatible a →
        embed a u = embed b v → b = a) ∧
      3 * (targets.card * Fintype.card Block * K) ≤
        8 * (Fintype.card State *
          ∑ a ∈ selected targets ambient events x y w,
            (nonholes (selected targets ambient events x y w) embed compatible a).card) := by sorry
