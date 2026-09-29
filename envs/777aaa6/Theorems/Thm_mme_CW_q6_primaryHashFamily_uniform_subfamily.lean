-- Prove2me | Theorems.Thm_mme_CW_q6_primaryHashFamily_uniform_subfamily
-- name    : mme_CW_q6_primaryHashFamily_uniform_subfamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:35:23.681028+00:00
-- url     : https://prove2.me/theorems/bf15777f-adb9-4293-a7ac-ed27a589747b
-- title:
--   Uniform fiber selection preserves the q=6 primary hash family structure
-- statement:
--   Let $P$ be a retained set of entries of a q=6 primary hash family, and let `outer` be a selected set of outer fibers.  If every selected fiber contains at least $H'>0$ entries of $P$, with $H'\leq H$, then choosing exactly $H'$ entries in each selected fiber produces a new primary hash family with $|\mathrm{outer}|$ fibers of size $H'$.  Moreover, every pointwise address property satisfied by entries of $P$ is satisfied by every entry of the new family.
--
--   The result preserves all structural axioms of the primary hash family, including X/Y injectivity, common Z words inside fibers, Z separation between fibers, and the induced condition.  It is the uniformization bridge used after common-half double counting.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, primary hash families and paired 121/211 analysis; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem mme_CW_q6_primaryHashFamily_uniform_subfamily
    {N L G A H H' : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (P : Finset (Fin A × Fin H)) (outer : Finset (Fin A))
    (Good : CWQ6ExactCoupledAddress N L G → Prop)
    (hH' : 0 < H') (hHle : H' ≤ H)
    (hfiber : ∀ a ∈ outer,
      H' ≤ (P.filter (fun p ↦ p.1 = a)).card)
    (hGood : ∀ p ∈ P, Good (family.entry p)) :
    ∃ subfamily : CWQ6PrimaryHashFamily N L G outer.card H',
      (∀ p, Good (subfamily.entry p)) ∧ H' ≤ H := by
  sorry
