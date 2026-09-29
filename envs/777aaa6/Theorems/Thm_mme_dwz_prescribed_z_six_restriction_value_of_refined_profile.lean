-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
-- name    : mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T02:04:22.64416+00:00
-- url     : https://prove2.me/theorems/eec6bbce-8f0b-4730-b859-4bf53e49dec8
-- title:
--   Prescribed-Z restriction value transfers from a refined profile to its reduced form
-- statement:
--   Let $T$ be a tensor over a field $K$, let $b_Z$ be a basis of its third mode, and let $\mathrm{grade}$ assign to each basis index one of $t$ Z-classes. An integer Z-split profile $p$ is a denominator $D_p$ together with counts $c_p(a)$ summing to $D_p$; the prescribed Z-power $T^{[p]}_m$ is the Z-coordinate projection of $T^{\otimes D_p m}$ onto the words whose left-grade histogram is exactly $c_p(\cdot)\,m$.
--
--   Suppose two profiles describe the same distribution, one of them refined by an integer factor $k \ge 1$:
--
--   $$D_q = D_p\,k, \qquad c_q(a) = c_p(a)\,k \quad \text{for every } a .$$
--
--   Then every restriction-based six-symmetrized value certificate for $q$ is also one for $p$:
--
--   $$V^{(6)}_{\tau}\big(T, b_Z, \mathrm{grade}, q\big) \ge V \;\Longrightarrow\; V^{(6)}_{\tau}\big(T, b_Z, \mathrm{grade}, p\big) \ge V .$$
--
--   The reason is that the two prescribed powers coincide after reindexing: $q$ at multiplicity $m$ and $p$ at multiplicity $km$ have the same word length $D_p k m$ and impose the same histogram condition $c_p(a)\,km$. The certificate quantifies over cofinal multiplicities, so the witnesses produced for $q$ at $m$ serve $p$ at $km$, and every cutoff is still met because $k \ge 1$.
--
--   This is the bookkeeping bridge between a component value proved with the denominator in which its data were published and the same value stated with the reduced denominator used by a ledger or table. It transfers a certificate; it asserts no new value, and the converse direction (from $p$ to $q$) is not claimed, since it would require witnesses at multiplicities divisible by $k$.
-- source:
--   Bookkeeping bridge for Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9: the restricted-splitting value of a prescribed Z-profile is unchanged when the profile's denominator and counts are scaled by a common positive integer. Used to state a component value with the reduced denominator of a ledger row rather than the denominator in which its data were published.

import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZRestrictedValue Module
universe u
set_option autoImplicit false

theorem mme_dwz_prescribed_z_six_restriction_value_of_refined_profile {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p q : IntegerZSplitProfile t) (k : ℕ) (hk : 0 < k)
    (hden : q.denominator = p.denominator * k)
    (hcount : ∀ a, q.count a = p.count a * k)
    (tau V : ℝ)
    (h : HasPrescribedZSixRestrictionValueAtLeast T bZ grade q tau V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V := by sorry
